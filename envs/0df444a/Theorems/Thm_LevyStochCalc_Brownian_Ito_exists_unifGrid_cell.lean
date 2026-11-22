-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_unifGrid_cell
-- name    : LevyStochCalc.Brownian.Ito.exists_unifGrid_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:21:36.416441+00:00
-- url     : https://prove2.me/theorems/5543ef95-6d6c-45c2-b6ad-3e9d914bbd20
-- title:
--   exists unifGrid cell
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` is extracted from `LevyStochCalc.Brownian.ItoFormulaGrid`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The uniform grid and the third-moment remainder

The uniform partition of `[0, T]` into `m` cells, and the bound it gives for the sum of third
absolute moments of the increments of an Itô process — the size of the Taylor remainder in
Itô's formula.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid` — the uniform grid on `[0, T]`.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid` — the simple integrand carried by
  the uniform grid.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le` — the sum of third absolute
  moments of the Itô-integral increments across the grid, of order `m^{-1/2}`.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le` — the same for the
  increments of a full Itô process, drift included.
* `LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid` — the Riemann sums of a
  continuous weight against a bounded density converge as the grid refines.
* `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` — every time in `(0, T]` lies in a cell.
* `LevyStochCalc.Brownian.Ito.abs_ofUnifGrid_eval_sub_le` — the grid step weight is within the
  weight's modulus of continuity at the mesh.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound` — a uniform pathwise bound on
  `(0, T]` gives the `L²` distance over the window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.exists_unifGrid_cell {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {s : ℝ}
    (hs : 0 < s) (hsT : s ≤ T) :
    ∃ i : ℕ, i < m ∧ unifGrid T m i < s ∧ s ≤ unifGrid T m (i + 1) := by sorry
