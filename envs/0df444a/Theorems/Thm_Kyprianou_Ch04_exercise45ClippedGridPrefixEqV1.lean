-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ClippedGridPrefixEqV1
-- name    : Kyprianou.Ch04.exercise45ClippedGridPrefixEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:18:56.371312+00:00
-- url     : https://prove2.me/theorems/8ff4f5e0-d8e4-5661-9ddb-dfbe58837e2d
-- title:
--   Clipped grid sums agree when left weights agree up to the clock
-- statement:
--   For two arbitrary left weights that agree up to a fixed evaluation clock, the clipped grid sums against the same process are equal.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation argument.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Two clipped grids agree before a common clock whenever their left weights agree there. -/
theorem Kyprianou.Ch04.exercise45ClippedGridPrefixEqV1 {Ω : Type}
    (X H K : NNReal → Ω → ℝ) (w : Ω) (T t : NNReal) (j : ℕ)
    (h : ∀ u ≤ t, H u w = K u w) :
    (∑ k ∈ Finset.range j,
      let u : NNReal := T * (k : NNReal) / (j : NNReal)
      let v : NNReal := T * ((k+1 : ℕ) : NNReal) / (j : NNReal)
      H u w * (X (min t v) w - X (min t u) w)) =
    (∑ k ∈ Finset.range j,
      let u : NNReal := T * (k : NNReal) / (j : NNReal)
      let v : NNReal := T * ((k+1 : ℕ) : NNReal) / (j : NNReal)
      K u w * (X (min t v) w - X (min t u) w)) := by
  sorry
