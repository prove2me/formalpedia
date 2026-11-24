-- Prove2me | Theorems.Thm_GlobalTheory_exists_graded_surjection
-- name    : GlobalTheory.exists_graded_surjection
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:28.826079+00:00
-- url     : https://prove2.me/theorems/c4011de6-0d71-41ac-9cd0-146e83b0b4d8
-- title:
--   Global Theory: exists graded surjection
-- statement:
--   The Global Theory construction uses the exists graded surjection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L500-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L500-L517

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R] {κ : Type*}
  {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]

theorem GlobalTheory.exists_graded_surjection (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩] [PolyGradedSMul ι 𝒩]
    [Module.Finite (MvPolynomial ι R) N] :
    ∃ (r : ℕ) (d : Fin r → ℤ) (f : (Fin r → MvPolynomial ι R) →ₗ[MvPolynomial ι R] N),
      IsGradedMap (grFree ι R d) 𝒩 f ∧ Function.Surjective f := by sorry
