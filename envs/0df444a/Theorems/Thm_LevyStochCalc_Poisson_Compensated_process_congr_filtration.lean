-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_process_congr_filtration
-- name    : LevyStochCalc.Poisson.Compensated.process_congr_filtration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:33:56.804211+00:00
-- url     : https://prove2.me/theorems/fa087203-8da9-4b04-a2ca-cec316fe6d88
-- title:
--   process congr filtration
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.process_congr_filtration` is extracted from `LevyStochCalc.Brownian.ItoFiltrationChange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFiltrationChange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The stochastic integrals under a change of filtration

The `L²` Brownian Itô integral and the `L²` Itô–Lévy integral against a compensated Poisson
random measure are each assembled from an approximating sequence of elementary integrands
selected relative to a filtration, so one integrand integrated against one driver over two
filtrations gives two constructions. The elementary integral of such an approximant mentions no
filtration, and the `L²` distance between two elementary integrals, or between an elementary
integral and the limit, is the energy of the difference of the integrands; both constructions
are therefore the `L²`-limit of a single sequence, and they agree almost everywhere. Passing to
the augmented filtration is the case of interest, since that filtration satisfies the usual
conditions.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration` — the Brownian
  integral over `ℱ` agrees almost everywhere with the integral over a larger filtration.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_augFiltration` — the Brownian integral
  over `ℱ` agrees almost everywhere with the integral over `augFiltration ℱ P`.
* `LevyStochCalc.Poisson.Compensated.process_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_augFiltration` — the same three
  statements for the compensated Poisson integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory
open scoped NNReal ENNReal

universe v
universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

theorem _root_.LevyStochCalc.Poisson.Compensated.process_congr_filtration
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (h𝒢 : IsPoissonFiltration N 𝒢)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hp' : Probability.MarkedProgressivelyMeasurable 𝒢 φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) :
    process N ℱ hℱ φ hm hp hq T =ᵐ[P] process N 𝒢 h𝒢 φ hm hp' hq T := by sorry
