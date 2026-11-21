-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_PathRegularity_existsUnique_mem_cell
-- name    : LevyStochCalc.BSDEJ.PathRegularity.existsUnique_mem_cell
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:31:25.907345+00:00
-- url     : https://prove2.me/theorems/0c17c690-e1dd-46c6-931b-afdf4789d366
-- title:
--   existsUnique mem cell
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.PathRegularity.existsUnique_mem_cell` is extracted from `LevyStochCalc.BSDEJ.CellAverageRate`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRate_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for a deterministic Lipschitz integrand

For a function `h : ℝ → ℝ` with `|h s - h t| ≤ K * |s - t|` and a strictly monotone partition
`0 = t_0 < ⋯ < t_M = T` of mesh at most `δ`, the pathwise average of `h` over the cell
`(t_n, t_{n+1}]` containing `s` differs from `h s` by at most `K * δ`, so the energy of
`h - cellTimeAverage_Z π h` over the horizon `[0, T]` is at most `(K * δ) ^ 2 * T`.

The integrand treated here is deterministic: it is the process `Z s ω i = h s`, constant in the
sample point and in the coordinate. The cell-average rate for a random integrand is a different,
genuinely stochastic statement and is not covered by anything below.
-/

open MeasureTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u

section Lipschitz

variable {K : ℝ} {h : ℝ → ℝ}

end Lipschitz

section Cells

variable {M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}

theorem _root_.LevyStochCalc.BSDEJ.PathRegularity.existsUnique_mem_cell (hmono : StrictMono π) (h0 : π 0 = 0) (hT : π (Fin.last M) = T)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T) :
    ∃! n : Fin M, π n.castSucc < s ∧ s ≤ π n.succ := by sorry
