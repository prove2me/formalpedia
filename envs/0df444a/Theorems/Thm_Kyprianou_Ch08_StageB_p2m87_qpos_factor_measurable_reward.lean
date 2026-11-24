-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_measurable_reward
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_factor_measurable_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T03:49:16.162382+00:00
-- url     : https://prove2.me/theorems/7a0154aa-50ef-402d-be6e-f58c7f73db2f
-- title:
--   Measurable right-continuous killed occupation reward
-- statement:
--   For a positive initial level and any measurable state set, there is a measurable reward functional on paths which equals the discounted occupation of the path killed at its lower passage on every right-continuous path started at zero.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_factor_measurable_reward
    (q a : ℝ) (ha : 0 < a) (A : Set ℝ) (hA : MeasurableSet A) :
    ∃ reward : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable reward ∧
      ∀ (y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) →
        y 0 = 0 →
        reward y =
          (∫⁻ s : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
            (if (s : WithTop ℝ≥0) <
                  tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧
                a + y s ∈ A
             then (1 : ℝ≥0∞) else 0) ∂positiveTimeLebesgue) := by
  sorry
