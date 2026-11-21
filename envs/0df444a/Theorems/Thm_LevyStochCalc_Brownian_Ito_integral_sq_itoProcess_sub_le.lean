-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_itoProcess_sub_le
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:19:19.365971+00:00
-- url     : https://prove2.me/theorems/2b58b936-ccde-4e48-935d-1c1bf42370e0
-- title:
--   integral sq itoProcess sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le` is extracted from `LevyStochCalc.Brownian.ItoProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô processes and the moments of their increments

An Itô process is `X_t = X₀ + ∫_{[0,t]} b_s ds + ∫_0^t H_s dW_s` for a bounded drift `b` and an
`L²` integrand `H`. Its increment across a window is the drift's window integral plus the Itô
integral's increment, so its moments follow from the drift bound and the increment moments of
the Itô integral.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoProcess` — the process itself.
* `LevyStochCalc.Brownian.Ito.itoProcess_sub` — the increment splits into drift and martingale
  parts.
* `LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le` — `𝔼|ΔX|² ≤ 2B²(Δt)² + 2C²Δt`.
* `LevyStochCalc.Brownian.Ito.integral_abs_sub_stochasticIntegral_le` — `𝔼|ΔM| ≤ C√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integral_abs_itoProcess_sub_le` — `𝔼|ΔX| ≤ BΔt + C√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integrable_abs_itoIncrement_pow_three` — the cube of the absolute
  increment is integrable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Drift

variable {P : Measure Ω} [IsProbabilityMeasure P]

end Drift

section Process

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le
    (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    MeasureTheory.Integrable (fun ω : Ω =>
        (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω) ^ 2) P
      ∧ ∫ ω, (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
            - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω) ^ 2 ∂P
          ≤ 2 * (B * (v - u)) ^ 2 + 2 * (C ^ 2 * (v - u)) := by sorry
