-- Prove2me | Theorems.Thm_GlobalTheory_isGradedMap_piSingle
-- name    : GlobalTheory.isGradedMap_piSingle
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:08.858807+00:00
-- url     : https://prove2.me/theorems/01c14d6d-1473-57e7-a3ae-0e58238e5b74
-- title:
--   Global Theory: is Graded Map pi Single
-- statement:
--   The Global Theory construction uses the is Graded Map pi Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L476-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L476-L481

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

theorem GlobalTheory.isGradedMap_piSingle [DecidableEq κ] (ℳ : ∀ k, ℤ → Submodule R (M k)) (k : κ) :
    IsGradedMap (ℳ k) (grPi ℳ) (LinearMap.single (MvPolynomial ι R) M k) := by sorry
