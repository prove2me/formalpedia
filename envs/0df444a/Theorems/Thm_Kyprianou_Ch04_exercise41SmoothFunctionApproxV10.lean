-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SmoothFunctionApproxV10
-- name    : Kyprianou.Ch04.exercise41SmoothFunctionApproxV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:41:24.993379+00:00
-- url     : https://prove2.me/theorems/ecd8262a-3294-4a23-9232-2c4c39e284f4
-- title:
--   Uniformly locally Lipschitz smooth approximants of a continuous function with a single derivative kink
-- statement:
--   Uniformly locally Lipschitz smooth approximants of a continuous function with a single derivative kink
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

theorem Kyprianou.Ch04.exercise41SmoothFunctionApproxV10
    (fLeft fRight : ℝ → ℝ)
    (hC1Left : ContDiff ℝ 1 fLeft) (hC1Right : ContDiff ℝ 1 fRight) :
    let G := fun x : ℝ => if x < 0 then fLeft x - fLeft 0
        else if 0 < x then fRight x - fRight 0 else 0
    let D := fun x : ℝ => if x < 0 then deriv fLeft x
        else if 0 < x then deriv fRight x else 0
    ∃ g : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (g n)) ∧
      (∀ x, Tendsto (fun n => g n x) atTop (𝓝 (G x))) ∧
      (∀ x, Tendsto (fun n => deriv (g n) x) atTop (𝓝 (D x))) ∧
      (∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        ∀ n x, |x| ≤ R → ‖deriv (g n) x‖ ≤ K) := by
  sorry
