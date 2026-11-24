-- Prove2me | Theorems.Thm_GlobalTheory_isGradedMap_lsmul
-- name    : GlobalTheory.isGradedMap_lsmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:20:08.051646+00:00
-- url     : https://prove2.me/theorems/ad2a0923-7671-4235-85a9-7b6c77b490cb
-- title:
--   Global Theory: is Graded Map lsmul
-- statement:
--   The Global Theory construction uses the is Graded Map lsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L287-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L287-L290

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
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]

theorem GlobalTheory.isGradedMap_lsmul (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {p : MvPolynomial ι R}
    {d : ℤ} (hp : p ∈ polyGrading ι R d) :
    IsGradedMap ℳ (grShift ℳ d) (LinearMap.lsmul (MvPolynomial ι R) M p) := by sorry
