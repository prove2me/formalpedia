-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_tendsto_lintegral_restrictedStage_sub_pathwise
-- name    : LevyStochCalc.Poisson.Compensated.tendsto_lintegral_restrictedStage_sub_pathwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:13:18.085793+00:00
-- url     : https://prove2.me/theorems/d7308af4-0f74-4b1d-a8e9-513296246cea
-- title:
--   tendsto lintegral restrictedStage sub pathwise
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.tendsto_lintegral_restrictedStage_sub_pathwise` is extracted from `LevyStochCalc.Poisson.PathwiseIdentity`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of a predictable integrand is pathwise

The compensated integral is an `L²` limit of the integrals of mark-step approximants. For a
predictable integrand carried by a window of finite intensity the approximants can be taken
inside that window, where the reference intensity compensates the counts, so their pathwise forms
converge in mean to the pathwise form of the integrand while their integrals converge in `L²` to
the compensated integral. The two limits therefore agree.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Assembly

variable (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  {A : Set E} (hA : MeasurableSet A)

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.tendsto_lintegral_restrictedStage_sub_pathwise
    (hφpred : Probability.MarkedPredictable ℱ ν φ) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => ∫⁻ ω,
      ‖(restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n).integral N T ω
        - ((∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(N.N ω))
          - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(referenceIntensity ν))‖ₑ ∂P)
      atTop (𝓝 0) := by sorry
