-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_taylorRemainder_le
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:35:15.233511+00:00
-- url     : https://prove2.me/theorems/855e793b-532d-4d06-a79d-a796596e62a7
-- title:
--   integral abs taylorRemainder le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le` is extracted from `LevyStochCalc.Brownian.ItoFormula`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormula_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Grid Riemann sums of the Itô integral

The weighted sum of the Itô integral's increments across a uniform grid is itself an Itô
integral — that of the grid's step weight against the integrand — and replacing the step weight
by a general one costs the `L²` distance between them times the bound on the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae` — the grid-weighted sum of increments as
  an Itô integral.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sum_unifGrid_sub_le` — that sum is `L²`-close to the
  Itô integral of the weight, with the weight's modulus of continuity as the rate.
* `LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le` — the second-order Taylor
  remainder along a uniform grid is `O(m^{-1/2})` in `L¹`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section GridSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end GridSum

section TaylorRemainder

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le
    {X₀ : Ω → ℝ} (hX₀ : Measurable X₀) (bdrift : Ω → ℝ → ℝ)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => taylorRemainder f f' f''
        (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m) P
      ∧ ∫ ω, |taylorRemainder f f' f''
          (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m| ∂P
        ≤ K * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
          + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
            * (T * Real.sqrt (T / (m : ℝ))))) := by sorry
