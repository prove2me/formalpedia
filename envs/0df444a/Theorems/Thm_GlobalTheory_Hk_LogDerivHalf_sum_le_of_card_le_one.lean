-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LogDerivHalf_sum_le_of_card_le_one
-- name    : GlobalTheory.Hk.LogDerivHalf.sum_le_of_card_le_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:35:22.671224+00:00
-- url     : https://prove2.me/theorems/d7873448-08a7-418b-b7c4-f81f369cf58e
-- title:
--   Log Deriv Half: sum le of card le one
-- statement:
--   The Log Deriv Half construction uses the sum le of card le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean#L83-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivSubExceptionalLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDerivHalf

theorem GlobalTheory.Hk.LogDerivHalf.sum_le_of_card_le_one {ι : Type*} {Z : Finset ι} (hZ : Z.card ≤ 1) {f : ι → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ∈ Z, ‖f i‖ ≤ M) : ‖∑ i ∈ Z, f i‖ ≤ M := by sorry
