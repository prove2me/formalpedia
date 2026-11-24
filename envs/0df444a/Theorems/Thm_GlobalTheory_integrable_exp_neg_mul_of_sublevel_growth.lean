-- Prove2me | Theorems.Thm_GlobalTheory_integrable_exp_neg_mul_of_sublevel_growth
-- name    : GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:22.066166+00:00
-- url     : https://prove2.me/theorems/efaf4756-bb99-48c7-b1ee-59a3e76e6f2c
-- title:
--   Global Theory: integrable exp neg mul of sublevel growth
-- statement:
--   The Global Theory construction uses the integrable exp neg mul of sublevel growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegrableExpNegMulOfSublevelGrowth.lean#L7-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegrableExpNegMulOfSublevelGrowth.lean#L7-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulOfSublevelGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d →
      (∀ x, 0 ≤ d x) →
      (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b →
      Integrable (fun x => Real.exp (-(b * d x))) μ := by sorry
