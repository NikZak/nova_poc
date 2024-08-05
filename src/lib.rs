use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};
use generic_array::typenum::U2;
use neptune::{circuit2::poseidon_hash_allocated, poseidon::PoseidonConstants, Strength};
use nova_snark::traits::{circuit::StepCircuit, Group};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct PoseidonStepCircuit<G: Group> {
    _group: PhantomData<G>,
}

impl<G: Group> Default for PoseidonStepCircuit<G> {
    fn default() -> Self {
        Self::new()
    }
}

impl<G: Group> PoseidonStepCircuit<G> {
    pub fn new() -> Self {
        Self {
            _group: PhantomData,
        }
    }
}

impl<G: Group> StepCircuit<G::Scalar> for PoseidonStepCircuit<G> {
    fn arity(&self) -> usize {
        2
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
        &self,
        cs: &mut CS,
        z_in: &[AllocatedNum<G::Scalar>],
    ) -> Result<Vec<AllocatedNum<G::Scalar>>, SynthesisError> {
        // z_in[0] is the current step index, z_in[1] provides the running digest,
        assert_eq!(z_in.len(), 2, "Invalid number of inputs: {}", z_in.len());

        // add 1 to step index to create next step index
        let one = AllocatedNum::alloc(cs.namespace(|| "one"), || Ok(1.into()))?;
        let new_step = z_in[0].add(&mut *cs, &one)?;
        let updated_inp = vec![new_step.clone(), z_in[1].clone()];

        let pc =
            PoseidonConstants::<<G as Group>::Scalar, U2>::new_with_strength(Strength::Standard);

        let digest = poseidon_hash_allocated(cs, updated_inp, &pc)?;

        Ok(vec![new_step, digest])
    }
}

/// cargo test --release -- --nocapture
#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;
    use flate2::{write::ZlibEncoder, Compression};
    use nova_snark::{
        provider::{Bn256EngineKZG, GrumpkinEngine},
        traits::{circuit::TrivialCircuit, snark::RelaxedR1CSSNARKTrait, Engine},
        CompressedSNARK, PublicParams, RecursiveSNARK,
    };

    use neptune::{poseidon::PoseidonConstants, Poseidon};
    use std::time::Instant;

    type E1 = Bn256EngineKZG;
    type E2 = GrumpkinEngine;
    type EE1 = nova_snark::provider::hyperkzg::EvaluationEngine<E1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
    type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

    fn off_circuit_poseidon_ivc<G: Group>(
        inputs: &[<G as Group>::Scalar],
    ) -> Vec<<G as Group>::Scalar> {
        let new_step = inputs[0] + (<G as Group>::Scalar::from(1));
        let pc =
            PoseidonConstants::<<G as Group>::Scalar, U2>::new_with_strength(Strength::Standard);
        let mut poseidon =
            Poseidon::<<G as Group>::Scalar, U2>::new_with_preimage(&[new_step, inputs[1]], &pc);
        let digest = poseidon.hash();
        vec![new_step, digest]
    }

    #[test]
    fn test_poseidon_chain() {
        let mut rng = rand::thread_rng();
        let v1 = <E1 as Engine>::Scalar::random(&mut rng);
        let inputs = [<E1 as Engine>::Scalar::ZERO, v1];

        println!("Inputs: {:?}", inputs);
        let num_steps = 10_usize;
        println!("Number of steps: {}", num_steps);
        let circuit_primary = PoseidonStepCircuit::new();
        let circuit_secondary = TrivialCircuit::default();

        // produce public parameters
        let start = Instant::now();
        println!("Producing public parameters...");
        let pp = PublicParams::<
            E1,
            E2,
            PoseidonStepCircuit<<E1 as Engine>::GE>,
            TrivialCircuit<<E2 as Engine>::Scalar>,
        >::setup(
            &circuit_primary,
            &circuit_secondary,
            &*S1::ck_floor(),
            &*S2::ck_floor(),
        )
        .unwrap();
        println!("PublicParams::setup, took {:?} ", start.elapsed());

        println!(
            "Number of constraints per step (primary circuit): {}",
            pp.num_constraints().0
        );
        println!(
            "Number of constraints per step (secondary circuit): {}",
            pp.num_constraints().1
        );

        println!(
            "Number of variables per step (primary circuit): {}",
            pp.num_variables().0
        );
        println!(
            "Number of variables per step (secondary circuit): {}",
            pp.num_variables().1
        );

        // produce non-deterministic advice
        let circuits = (0..num_steps.try_into().unwrap())
            .map(|_| PoseidonStepCircuit::new())
            .collect::<Vec<_>>();

        type C1 = PoseidonStepCircuit<<E1 as Engine>::GE>;
        type C2 = TrivialCircuit<<E2 as Engine>::Scalar>;

        // produce a recursive SNARK
        println!("Generating a RecursiveSNARK...");
        let mut recursive_snark: RecursiveSNARK<E1, E2, C1, C2> =
            RecursiveSNARK::<E1, E2, C1, C2>::new(
                &pp,
                &circuits[0],
                &circuit_secondary,
                &inputs,
                &[<E2 as Engine>::Scalar::zero()],
            )
            .unwrap();

        let mut poseidon_res = inputs.to_vec();
        for (i, circuit_primary) in circuits.iter().enumerate() {
            let start = Instant::now();
            let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
            assert!(res.is_ok());

            println!("RecursiveSNARK::prove {} : took {:?} ", i, start.elapsed());
            poseidon_res = off_circuit_poseidon_ivc::<<E1 as Engine>::GE>(&poseidon_res);
            assert_eq!(recursive_snark.outputs().0, poseidon_res);
        }
        println!("RecursiveSNARK::outputs: {:?}", recursive_snark.outputs());

        // verify the recursive SNARK
        println!("Verifying a RecursiveSNARK...");
        let res = recursive_snark.verify(&pp, num_steps, &inputs, &[<E2 as Engine>::Scalar::ZERO]);
        println!("RecursiveSNARK::verify: {:?}", res.is_ok(),);
        assert!(res.is_ok());

        // produce a compressed SNARK
        println!("Generating a CompressedSNARK using Spartan with HyperKZG...");
        let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

        let start = Instant::now();

        let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
        println!(
            "CompressedSNARK::prove: {:?}, took {:?}",
            res.is_ok(),
            start.elapsed()
        );
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
        let compressed_snark_encoded = encoder.finish().unwrap();
        println!(
            "CompressedSNARK::len {:?} bytes",
            compressed_snark_encoded.len()
        );

        // verify the compressed SNARK
        println!("Verifying a CompressedSNARK...");
        let start = Instant::now();
        let res = compressed_snark.verify(&vk, num_steps, &inputs, &[<E2 as Engine>::Scalar::ZERO]);
        println!(
            "CompressedSNARK::verify: {:?}, took {:?}",
            res.is_ok(),
            start.elapsed()
        );
        assert!(res.is_ok());
    }
}
