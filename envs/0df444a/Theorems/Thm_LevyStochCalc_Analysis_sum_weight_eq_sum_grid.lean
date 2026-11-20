-- Prove2me | Theorems.Thm_LevyStochCalc_Analysis_sum_weight_eq_sum_grid
-- name    : LevyStochCalc.Analysis.sum_weight_eq_sum_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:15:56.169269+00:00
-- url     : https://prove2.me/theorems/7105f87a-9dab-4bbd-bc40-c5c2f68a5680
-- title:
--   sum weight eq sum grid
-- statement:
--   The source theorem `LevyStochCalc.Analysis.sum_weight_eq_sum_grid` is extracted from `LevyStochCalc.Analysis.SortedGrid`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_SortedGrid_F000

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

theorem _root_.LevyStochCalc.Analysis.sum_weight_eq_sum_grid (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ)
    (v : Fin d → ℝ → ℝ) (hv : ∀ p : F, (p.1.2 : ℝ) ≤ 0 → v p.1.1 (p.1.2 : ℝ) = 0)
    {S : Finset ℝ} (hS : posTimes F ⊆ S) (hSpos : ∀ x ∈ S, 0 < x) :
    ∑ p : F, v p.1.1 (p.1.2 : ℝ) * w p
      = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          weightAt F w (sortedGrid S k) i * v i (sortedGrid S k) := by sorry
