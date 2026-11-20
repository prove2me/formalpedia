-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_aestronglyMeasurable_pathwise_count
-- name    : LevyStochCalc.Poisson.aestronglyMeasurable_pathwise_count
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:21:28.605713+00:00
-- url     : https://prove2.me/theorems/ceab451b-ef2f-4243-a351-c9bfc42b87cf
-- title:
--   aestronglyMeasurable pathwise count
-- statement:
--   The source theorem `LevyStochCalc.Poisson.aestronglyMeasurable_pathwise_count` is extracted from `LevyStochCalc.Poisson.CompensatorL1`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F003

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

theorem _root_.LevyStochCalc.Poisson.aestronglyMeasurable_pathwise_count (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : Ω → ℝ → E → ℝ}
    (hη : Probability.MarkedPredictable ℱ ν η)
    (hm : Measurable fun p : Ω × ℝ × E => η p.1 p.2.1 p.2.2)
    (hen : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P ≠ ⊤) :
    AEStronglyMeasurable
      (fun ω => ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(N.N ω)) P := by sorry
