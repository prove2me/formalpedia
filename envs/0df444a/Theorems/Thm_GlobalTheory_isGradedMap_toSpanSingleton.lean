-- Prove2me | Theorems.Thm_GlobalTheory_isGradedMap_toSpanSingleton
-- name    : GlobalTheory.isGradedMap_toSpanSingleton
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:44.087883+00:00
-- url     : https://prove2.me/theorems/e80d7194-93ee-40b9-839d-7076266ed9fa
-- title:
--   Global Theory: is Graded Map to Span Singleton
-- statement:
--   The Global Theory construction uses the is Graded Map to Span Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L297-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L297-L300

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

theorem GlobalTheory.isGradedMap_toSpanSingleton (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {m : M} {d : ℤ}
    (hm : m ∈ ℳ d) : IsGradedMap (grShift (polyGrading ι R) (-d)) ℳ
      (LinearMap.toSpanSingleton (MvPolynomial ι R) M m) := by sorry
