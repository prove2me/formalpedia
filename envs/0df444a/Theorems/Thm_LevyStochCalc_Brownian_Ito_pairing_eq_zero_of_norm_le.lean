-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_pairing_eq_zero_of_norm_le
-- name    : LevyStochCalc.Brownian.Ito.pairing_eq_zero_of_norm_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:54:42.286329+00:00
-- url     : https://prove2.me/theorems/dceb098a-7b08-400f-b0ac-510ac57b84df
-- title:
--   pairing eq zero of norm le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.pairing_eq_zero_of_norm_le` is extracted from `LevyStochCalc.Brownian.PRPPairing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing a weight orthogonal to the Itô integrals against a trigonometric increment

If `Z` pairs to zero against every Itô integral, then pairing it against `g (X_t)`, for `X` a
version of `∫ 1_{(a,b]} dW` and `g` one of the scaled trigonometric functions, gives a scalar
function of `t` that solves `Λ(t) = −(l²/2) ∫_0^t 1_{(a,b]}(s) Λ(s) ds`. Grönwall then forces
`Λ` to vanish.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Pairing

variable {P : Measure Ω} [IsProbabilityMeasure P]

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

variable {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

end Pairing

section Perp

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}

end Perp

section Equation

variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem _root_.LevyStochCalc.Brownian.Ito.pairing_eq_zero_of_norm_le {b : ℝ} {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ))
    {Y : Ω → ℂ} (hYm : Measurable Y) (hY : Integrable Y P) (hY0 : ∫ ω, Y ω ∂P = 0)
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hstep : ∀ t : ℝ, 0 < t → t ≤ b →
      ‖∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P‖
        ≤ l ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ) t, ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, ∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P = 0 := by sorry
