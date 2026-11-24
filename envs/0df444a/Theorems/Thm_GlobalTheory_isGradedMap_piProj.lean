-- Prove2me | Theorems.Thm_GlobalTheory_isGradedMap_piProj
-- name    : GlobalTheory.isGradedMap_piProj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:35.333591+00:00
-- url     : https://prove2.me/theorems/f6db7658-2312-4e45-9c22-678d4a935d63
-- title:
--   Global Theory: is Graded Map pi Proj
-- statement:
--   The Global Theory construction uses the is Graded Map pi Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L470-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L470-L472

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
variable (ι)

theorem GlobalTheory.isGradedMap_piProj (ℳ : ∀ k, ℤ → Submodule R (M k)) (k : κ) :
    IsGradedMap (grPi ℳ) (ℳ k) (LinearMap.proj (R := MvPolynomial ι R) k) := by sorry
