-- Prove2me | Theorems.Thm_LevyStochCalc_Analysis_le_sortedGrid_card
-- name    : LevyStochCalc.Analysis.le_sortedGrid_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:16:20.407044+00:00
-- url     : https://prove2.me/theorems/aa4b1d31-d667-4921-91f2-33c4291c8db0
-- title:
--   le sortedGrid card
-- statement:
--   The source theorem `LevyStochCalc.Analysis.le_sortedGrid_card` is extracted from `LevyStochCalc.Analysis.SortedGrid`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_SortedGrid_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The increasing enumeration of a finite family of times

`sortedGrid S` lists the elements of a finite set `S ⊆ ℝ` in increasing order at the indices
`1, …, #S`, and takes the value `0` at index `0` and beyond `#S`. When every element of `S` is
positive it is strictly increasing on `{0, …, #S}`.

A finite family of (coordinate, time) pairs carrying real weights is thereby rewritten as a sum
over such a grid: `posTimes` collects the strictly positive times of the family and `weightAt`
collects the weights sharing a coordinate and a time.
-/

namespace LevyStochCalc.Analysis

open Finset

variable (S : Finset ℝ)

variable {d : ℕ} {T : ℝ}

theorem _root_.LevyStochCalc.Analysis.le_sortedGrid_card {S : Finset ℝ} {x : ℝ} (hx : x ∈ S) :
    x ≤ sortedGrid S S.card := by sorry
