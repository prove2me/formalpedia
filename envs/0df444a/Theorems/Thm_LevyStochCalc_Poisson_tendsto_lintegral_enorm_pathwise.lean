-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_tendsto_lintegral_enorm_pathwise
-- name    : LevyStochCalc.Poisson.tendsto_lintegral_enorm_pathwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:17:12.484757+00:00
-- url     : https://prove2.me/theorems/f9a2cbc1-aa3d-4a01-9d2a-57d86a1d9d31
-- title:
--   tendsto lintegral enorm pathwise
-- statement:
--   The source theorem `LevyStochCalc.Poisson.tendsto_lintegral_enorm_pathwise` is extracted from `LevyStochCalc.Poisson.CompensatorL1`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}

end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}

theorem _root_.LevyStochCalc.Poisson.tendsto_lintegral_enorm_pathwise (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : ℕ → Ω → ℝ → E → ℝ}
    (hη : ∀ n, Probability.MarkedPredictable ℱ ν (η n))
    (hηm : ∀ n, Measurable fun p : Ω × ℝ × E => η n p.1 p.2.1 p.2.2)
    (hen : Tendsto (fun n => ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η n ω q.1 q.2 ∂(N.N ω))
      - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          η n ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ ∂P) atTop (𝓝 0) := by sorry
