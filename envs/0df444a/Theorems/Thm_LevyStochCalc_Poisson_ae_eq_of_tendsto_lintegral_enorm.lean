-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_ae_eq_of_tendsto_lintegral_enorm
-- name    : LevyStochCalc.Poisson.ae_eq_of_tendsto_lintegral_enorm
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:15:40.668464+00:00
-- url     : https://prove2.me/theorems/38b38663-e4ef-46bb-9755-8959cbcdea25
-- title:
--   ae eq of tendsto lintegral enorm
-- statement:
--   The source theorem `LevyStochCalc.Poisson.ae_eq_of_tendsto_lintegral_enorm` is extracted from `LevyStochCalc.Poisson.CompensatorL1`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F001

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

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Poisson.ae_eq_of_tendsto_lintegral_enorm {Y Z : Ω → ℝ} {X : ℕ → Ω → ℝ}
    (hY : AEStronglyMeasurable Y P) (hZ : AEStronglyMeasurable Z P)
    (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (h1 : Tendsto (fun n => ∫⁻ ω, ‖Y ω - X n ω‖ₑ ∂P) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Z ω‖ₑ ∂P) atTop (𝓝 0)) :
    Y =ᵐ[P] Z := by sorry
