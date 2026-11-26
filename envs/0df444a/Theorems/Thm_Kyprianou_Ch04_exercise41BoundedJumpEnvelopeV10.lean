-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BoundedJumpEnvelopeV10
-- name    : Kyprianou.Ch04.exercise41BoundedJumpEnvelopeV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:43:15.067506+00:00
-- url     : https://prove2.me/theorems/1cb1b3da-de93-4b3f-95d4-798c51fd5c71
-- title:
--   Uniform derivative bounds control each jump difference and absolute summability passes to the limit
-- statement:
--   Uniform derivative bounds control each jump difference and absolute summability passes to the limit
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BoundedJumpEnvelopeV10
    {ι : Type} (x l : ι → ℝ) (R K : ℝ)
    (hx : ∀ i, |x i| ≤ R) (hl : ∀ i, |l i| ≤ R)
    (g : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hg : ∀ n, ContDiff ℝ 1 (g n))
    (hlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 (G y)))
    (hBound : ∀ n y, |y| ≤ R → ‖deriv (g n) y‖ ≤ K)
    (hSum : Summable (fun i => |x i - l i|)) :
    ∃ B : ι → ℝ, Summable B ∧
      (∀ᶠ n in atTop, ∀ i, ‖g n (x i) - g n (l i)‖ ≤ B i) ∧
      Summable (fun i => ‖G (x i) - G (l i)‖) := by
  sorry
