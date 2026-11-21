-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_riemann_weighted_unifGrid
-- name    : LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:21:59.215175+00:00
-- url     : https://prove2.me/theorems/b2ecb2d8-ac56-4dbd-84d9-353832c8f12f
-- title:
--   tendsto riemann weighted unifGrid
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid` is extracted from `LevyStochCalc.Brownian.ItoFormulaGrid`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ThirdMomentSum

section RiemannLimit

theorem _root_.LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid {g h : ℝ → ℝ} (hgc : Continuous g)
    (hh : Measurable h) {M : ℝ} (hM0 : 0 ≤ M) (hhM : ∀ s, |h s| ≤ M) {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m,
        g (unifGrid T m i) * ∫ s in unifGrid T m i..unifGrid T m (i + 1), h s)
      Filter.atTop (nhds (∫ s in (0 : ℝ)..T, g s * h s)) := by sorry
