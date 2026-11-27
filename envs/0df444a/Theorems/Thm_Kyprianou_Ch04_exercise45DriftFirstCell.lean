-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45DriftFirstCell
-- name    : Kyprianou.Ch04.exercise45DriftFirstCell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:57:36.16534+00:00
-- url     : https://prove2.me/theorems/94f48593-acfe-4ed7-bbdb-65775f6a5ea6
-- title:
--   Deterministic drift grid at its first endpoint
-- statement:
--   At the first endpoint of the unit horizon clipped grid all increments but the first vanish.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), formal boundary audit.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- At the end of the first cell of the unit grid, only its weight contributes. -/
theorem Kyprianou.Ch04.exercise45DriftFirstCell (n : ℕ) (hn : 0 < n) (a : ℝ) :
    (∑ k ∈ Finset.range n,
      let u : NNReal := (1 : NNReal) * (k : NNReal) / (n : NNReal)
      let v : NNReal := (1 : NNReal) * ((k + 1 : ℕ) : NNReal) / (n : NNReal)
      (2 * (if u = 0 then a else (u : ℝ))) *
        (((min (1 / (n : NNReal)) v : NNReal) : ℝ) -
          ((min (1 / (n : NNReal)) u : NNReal) : ℝ))) =
        2 * a / (n : ℝ) := by
  sorry
