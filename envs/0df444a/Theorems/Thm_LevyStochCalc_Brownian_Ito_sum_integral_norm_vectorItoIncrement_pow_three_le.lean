-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_integral_norm_vectorItoIncrement_pow_three_le
-- name    : LevyStochCalc.Brownian.Ito.sum_integral_norm_vectorItoIncrement_pow_three_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:36:46.860595+00:00
-- url     : https://prove2.me/theorems/450a4f34-77bd-4101-8e84-29275e3d2226
-- title:
--   sum integral norm vectorItoIncrement pow three le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.sum_integral_norm_vectorItoIncrement_pow_three_le` is extracted from `LevyStochCalc.Brownian.VectorItoThirdMoment`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoThirdMoment_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Third absolute moments of a vector Itô process's increments

The second-order Taylor remainder of a function with Lipschitz second derivative is cubic in the
increment, so Itô's formula in the vector setting needs the third absolute moment of `‖ΔX‖`. It
is assembled from the coordinatewise splitting: the supremum norm is controlled by the sum of the
coordinates, each coordinate by its drift part and its martingale part, and the martingale part
by the individual Itô increments.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_abs_sum_pow_three_le` — the third absolute moment of a
  finite sum.
* `LevyStochCalc.Brownian.Ito.integral_norm_pi_pow_three_le` — the third moment of the supremum
  norm from the coordinates.
* `LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_pow_three_le` —
  `𝔼‖ΔX‖³ ≤ 4n³((BΔt)³ + d³κ Δt√(Δt))` with `κ = (C² + (6+c)C⁴)/2`.
* `LevyStochCalc.Brownian.Ito.sum_integral_norm_vectorItoIncrement_pow_three_le` — the same
  summed over a uniform grid, of order `m^{-1/2}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section GenericThird

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end GenericThird

section VectorThird

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.sum_integral_norm_vectorItoIncrement_pow_three_le (X₀ : Ω → Fin n → ℝ)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ m, Measurable (Function.uncurry (bdrift m)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, ∫ ω,
        ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3 ∂P
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ)))))))) := by sorry
