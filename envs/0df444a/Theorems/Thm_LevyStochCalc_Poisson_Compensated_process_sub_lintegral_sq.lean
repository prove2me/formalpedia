-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_process_sub_lintegral_sq
-- name    : LevyStochCalc.Poisson.Compensated.process_sub_lintegral_sq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:57:09.669742+00:00
-- url     : https://prove2.me/theorems/0eb1dad4-01ab-4a36-91c5-ced2ab1aa701
-- title:
--   process sub lintegral sq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.process_sub_lintegral_sq` is extracted from `LevyStochCalc.Poisson.CompensatedDiff`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDiff_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The difference isometry of the compensated integral process

For two integrands `φ₁, φ₂`, the `L²` integral processes satisfy
`∫⁻ ‖F₁(t) − F₂(t)‖² = ∫⁻∫⁻_{[0,t]}∫⁻ ‖φ₁ − φ₂‖²`: the stage approximants of the two
integrands are refined to a common dyadic grid, where the difference isometry of mark-step
integrands holds at every time, and both sides pass to the limit in `L²`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ₁ φ₂ : Ω → ℝ → E → ℝ)
  (h_meas₁ : Measurable (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2))
  (h_meas₂ : Measurable (fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2))
  (h_progMeas₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
  (h_progMeas₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
  (h_sq₁ : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (h_sq₂ : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.process_sub_lintegral_sq {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
        - process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by sorry
