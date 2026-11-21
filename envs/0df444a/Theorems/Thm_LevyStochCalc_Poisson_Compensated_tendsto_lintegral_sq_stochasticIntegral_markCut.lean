-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_tendsto_lintegral_sq_stochasticIntegral_markCut
-- name    : LevyStochCalc.Poisson.Compensated.tendsto_lintegral_sq_stochasticIntegral_markCut
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:14:52.699616+00:00
-- url     : https://prove2.me/theorems/743c4d95-11cb-4b87-bd72-37b812a11074
-- title:
--   tendsto lintegral sq stochasticIntegral markCut
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.tendsto_lintegral_sq_stochasticIntegral_markCut` is extracted from `LevyStochCalc.Poisson.SmallJump`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Theorems.Thm_LevyStochCalc_Probability_MarkedProgressivelyMeasurable_indicator_mark
import Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral over a shrinking family of marks

Restricting an admissible integrand to a measurable set of marks keeps it admissible, and by the
Itô–Lévy isometry the `L²` size of its compensated integral is the energy carried by that set.
Along an antitone family of mark sets whose intersection is null, that energy vanishes by
dominated convergence on the intensity, so the compensated integrals tend to `0` in `L²`.

## Main statements

* `LevyStochCalc.Poisson.Compensated.markCut` — an integrand restricted to a set of marks.
* `LevyStochCalc.Poisson.Compensated.tendsto_lintegral_sq_stochasticIntegral_markCut` — the
  compensated integrals over a shrinking family of marks tend to `0` in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Cut

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Cut

section Tendsto

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.tendsto_lintegral_sq_stochasticIntegral_markCut
    (A : ℕ → Set E) (hA : ∀ m, MeasurableSet (A m)) (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (A m) φ)
        (measurable_markCut h_meas (hA m)) (h_progMeas.indicator_mark (hA m))
        (fun T' hT' => sq_markCut h_sq (A m) T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (𝓝 0) := by sorry
