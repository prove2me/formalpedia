-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_lintegral_enorm_le_energy
-- name    : LevyStochCalc.Poisson.lintegral_enorm_le_energy
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:14:05.30464+00:00
-- url     : https://prove2.me/theorems/21afe54d-5120-44a0-aa74-92c21ab37439
-- title:
--   lintegral enorm le energy
-- statement:
--   The source theorem `LevyStochCalc.Poisson.lintegral_enorm_le_energy` is extracted from `LevyStochCalc.Poisson.CompensatorL1`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F000

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

omit [SigmaFinite ν] in

theorem _root_.LevyStochCalc.Poisson.lintegral_enorm_le_energy (hRfin : referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤)
    {η : Ω → ℝ → E → ℝ} (hη : Measurable fun p : Ω × ℝ × E => η p.1 p.2.1 p.2.2) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P
      ≤ (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            ‖η ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹
        * referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹ := by sorry
