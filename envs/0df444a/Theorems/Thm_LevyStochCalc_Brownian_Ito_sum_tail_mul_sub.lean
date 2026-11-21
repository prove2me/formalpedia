-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_tail_mul_sub
-- name    : LevyStochCalc.Brownian.Ito.sum_tail_mul_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:09:03.868423+00:00
-- url     : https://prove2.me/theorems/f136b265-5929-4b08-ba37-fa8f3ffda1e0
-- title:
--   sum tail mul sub
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.sum_tail_mul_sub` is extracted from `LevyStochCalc.Brownian.PRPGrid`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation over a grid

Iterating the one-window statement over the cells of a grid: a square-integrable weight of mean
zero and orthogonal to every Itô integral is orthogonal to every character of the increments of a
Brownian motion along a grid.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Grid

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

end Grid

section Abel

theorem _root_.LevyStochCalc.Brownian.Ito.sum_tail_mul_sub (c : ℕ → ℝ) {Wv : ℕ → ℝ} (h0 : Wv 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k)
      = ∑ k ∈ Finset.Ico 1 (n + 1), c k * Wv k := by sorry
