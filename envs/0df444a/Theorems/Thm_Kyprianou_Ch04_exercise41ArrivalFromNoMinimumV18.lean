-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ArrivalFromNoMinimumV18
-- name    : Kyprianou.Ch04.exercise41ArrivalFromNoMinimumV18
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T13:17:23.643561+00:00
-- url     : https://prove2.me/theorems/5f9d6437-a2cb-52e3-b194-6e3a239cee6f
-- title:
--   No positive jumps, isolated zeros and exclusion of zero local minima imply negative left germ
-- statement:
--   No positive jumps, isolated zeros and exclusion of zero local minima imply negative left germ
-- source:
--   Kyprianou (2006), Exercise 4.1(ii)

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ArrivalFromNoMinimumV18
    (x : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNeg : ∀ s l, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds l) → x s ≤ l)
    (hVisits : ∀ t : NNReal, Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ x s = 0})
    (hDep : ∀ s : NNReal, x s = 0 → ∃ e : NNReal, 0 < e ∧
      ∀ u : NNReal, 0 < u → u < e → 0 < x (s + u))
    (hMin : ∀ s : NNReal, 0 < s → x s = 0 →
      ¬ (∃ e : NNReal, 0 < e ∧ ∀ u ∈ Icc (s - e) (s + e), 0 ≤ x u)) :
    ∀ s : NNReal, 0 < s → x s = 0 → Function.leftLim x s = 0 →
      ∃ e : NNReal, 0 < e ∧ ∀ u : NNReal, 0 < u → u < min e s → x (s-u) < 0 := by
  sorry
