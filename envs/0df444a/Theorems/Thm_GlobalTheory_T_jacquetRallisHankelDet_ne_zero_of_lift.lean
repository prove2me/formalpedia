-- Prove2me | Theorems.Thm_GlobalTheory_T_jacquetRallisHankelDet_ne_zero_of_lift
-- name    : GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:26.685795+00:00
-- url     : https://prove2.me/theorems/57b97df2-0760-505a-9785-8446e3913fbe
-- title:
--   T: jacquet Rallis Hankel Det ne zero of lift
-- statement:
--   The T construction uses the jacquet Rallis Hankel Det ne zero of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLiftStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLiftStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLiftStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k), Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by sorry
