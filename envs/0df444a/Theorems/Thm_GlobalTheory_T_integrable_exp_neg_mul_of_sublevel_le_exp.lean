-- Prove2me | Theorems.Thm_GlobalTheory_T_integrable_exp_neg_mul_of_sublevel_le_exp
-- name    : GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:46:43.260288+00:00
-- url     : https://prove2.me/theorems/b2fb5bdf-4bc7-4f0b-8338-355e8ad47961
-- title:
--   T: integrable exp neg mul of sublevel le exp
-- statement:
--   The T construction uses the integrable exp neg mul of sublevel le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegrableExpNegMulOfSublevelGrowthStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegrableExpNegMulOfSublevelGrowthStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulOfSublevelGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulOfSublevelGrowthStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d → (∀ x, 0 ≤ d x) → (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b → Integrable (fun x => Real.exp (-(b * d x))) μ := by sorry
