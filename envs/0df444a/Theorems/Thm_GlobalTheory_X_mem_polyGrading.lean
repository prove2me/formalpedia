-- Prove2me | Theorems.Thm_GlobalTheory_X_mem_polyGrading
-- name    : GlobalTheory.X_mem_polyGrading
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:20:39.900105+00:00
-- url     : https://prove2.me/theorems/75675c97-5282-48ec-9ab7-167885297eee
-- title:
--   Global Theory: X mem poly Grading
-- statement:
--   The Global Theory construction uses the X mem poly Grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L76-L77

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
variable (ι : Type*) (R : Type*) [CommRing R]
variable {ι R}

theorem GlobalTheory.X_mem_polyGrading (i : ι) : (X i : MvPolynomial ι R) ∈ polyGrading ι R 1 := by sorry
