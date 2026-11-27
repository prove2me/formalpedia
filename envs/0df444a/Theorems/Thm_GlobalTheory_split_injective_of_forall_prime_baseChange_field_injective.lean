-- Prove2me | Theorems.Thm_GlobalTheory_split_injective_of_forall_prime_baseChange_field_injective
-- name    : GlobalTheory.split_injective_of_forall_prime_baseChange_field_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:40.943328+00:00
-- url     : https://prove2.me/theorems/10ea3379-d02c-5c3e-add4-19d280a04560
-- title:
--   Global Theory: split injective of forall prime base Change field injective
-- statement:
--   The Global Theory construction uses the split injective of forall prime base Change field injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplitInjectiveOfForallPrimeBaseChangeFieldInject.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplitInjectiveOfForallPrimeBaseChangeFieldInject.lean#L7-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitInjectiveOfForallPrimeBaseChangeFieldInject
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.split_injective_of_forall_prime_baseChange_field_injective :
    ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M] (N : Type 1) [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Module.Projective R N] (f : M →ₗ[R] N),
      (∀ P : PrimeSpectrum R, ∃ (k : Type) (_ : Field k) (_ : Algebra R k),
        RingHom.ker (algebraMap R k) = P.asIdeal ∧ Function.Injective (f.baseChange k)) →
      ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by sorry
