-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_tendsto_lintegral_enorm_of_eLpNorm
-- name    : LevyStochCalc.Poisson.tendsto_lintegral_enorm_of_eLpNorm
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T16:16:02.174169+00:00
-- url     : https://prove2.me/theorems/75b1f438-7f3f-4eab-bebd-c2801c4ce5f2
-- title:
--   tendsto lintegral enorm of eLpNorm
-- statement:
--   The source theorem `LevyStochCalc.Poisson.tendsto_lintegral_enorm_of_eLpNorm` is extracted from `LevyStochCalc.Poisson.CompensatorL1`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensator_F001

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

theorem _root_.LevyStochCalc.Poisson.tendsto_lintegral_enorm_of_eLpNorm {Y : Ω → ℝ} {X S : ℕ → Ω → ℝ}
    (hY : AEStronglyMeasurable Y P) (hS : ∀ n, AEStronglyMeasurable (S n) P)
    (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (h1 : Tendsto (fun n => eLpNorm (fun ω => S n ω - Y ω) 2 P) atTop (𝓝 0))
    (h2 : Tendsto (fun n => (∫⁻ ω, ‖S n ω - X n ω‖ₑ ^ 2 ∂P) ^ (2 : ℝ)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖Y ω - X n ω‖ₑ ∂P) atTop (𝓝 0) := by sorry
