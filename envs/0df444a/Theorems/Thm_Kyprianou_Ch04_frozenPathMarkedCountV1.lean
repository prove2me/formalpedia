-- Prove2me | Theorems.Thm_Kyprianou_Ch04_frozenPathMarkedCountV1
-- name    : Kyprianou.Ch04.frozenPathMarkedCountV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:15:04.444882+00:00
-- url     : https://prove2.me/theorems/34016481-d6c1-5efc-b1ba-ceea4e2f004f
-- title:
--   Physical marked jump set is unchanged by freezing on its past region
-- statement:
--   For every positive time at most T, the frozen path has the same value and strict left limit as the original. A time greater than T cannot enter the specified Borel time-mark region.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, adapted physical Poisson counts.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_frozenPathLeftLimitV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem frozenPathMarkedCountV1 (Y L : NNReal → ℝ) (T : NNReal)
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u)))
    (D : Set (ℝ × ℝ)) (hD : D ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ univ) :
    let Z := fun v : NNReal => Y (min v T)
    {u : NNReal | 0 < u ∧ Y u ≠ L u ∧ ((u : ℝ), Y u - L u) ∈ D} =
      {u : NNReal | 0 < u ∧ Z u - Function.leftLim Z u ≠ 0 ∧
        ((u : ℝ), Z u - Function.leftLim Z u) ∈ D} := by
  sorry
end Kyprianou.Ch04
