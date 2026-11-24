-- Prove2me | Theorems.Thm_GlobalTheory_T_summable_and_abs_tsum_exp_neg_qForm_sub_le
-- name    : GlobalTheory.T.summable_and_abs_tsum_exp_neg_qForm_sub_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:53.392364+00:00
-- url     : https://prove2.me/theorems/24a0bd3c-ba2b-44b0-9e3d-ca10573c5bf4
-- title:
--   T: summable and abs tsum exp neg q Form sub le
-- statement:
--   The T construction uses the summable and abs tsum exp neg q Form sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ThetaQFormStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ThetaQFormStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQFormStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.summable_and_abs_tsum_exp_neg_qForm_sub_le : ∀ α γ l θ₁ θ₂ t : ℝ, 0 < α → 0 < γ → 0 < t → Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧ |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) - Real.pi / Real.sqrt (α * γ) / t| ≤ Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2) := by sorry
