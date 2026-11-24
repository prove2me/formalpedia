-- Prove2me | Theorems.Thm_GlobalTheory_IsGradedMap_pi
-- name    : GlobalTheory.IsGradedMap.pi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:19.946698+00:00
-- url     : https://prove2.me/theorems/3f9cde30-6c83-4c61-b352-2a3b1f1ed3c9
-- title:
--   Is Graded Map: pi
-- statement:
--   The Is Graded Map construction uses the pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L483-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L483-L485

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

theorem GlobalTheory.IsGradedMap.pi {𝒩 : ℤ → Submodule R N} {ℳ : ∀ k, ℤ → Submodule R (M k)}
    {f : ∀ k, N →ₗ[MvPolynomial ι R] M k} (hf : ∀ k, IsGradedMap 𝒩 (ℳ k) (f k)) :
    IsGradedMap 𝒩 (grPi ℳ) (LinearMap.pi f) := by sorry
