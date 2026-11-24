-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_gelfA_eq_sum_pow
-- name    : GlobalTheory.SmoothForms.gelfA_eq_sum_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:45.099522+00:00
-- url     : https://prove2.me/theorems/ac529b98-a535-4228-97e7-604576125303
-- title:
--   Smooth Forms: gelf A eq sum pow
-- statement:
--   The Smooth Forms construction uses the gelf A eq sum pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean#L31-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] {n : ℕ}

theorem GlobalTheory.SmoothForms.gelfA_eq_sum_pow (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA E k = ∑ c, (Matrix.of E ^ (k + 1)) c c := by sorry
