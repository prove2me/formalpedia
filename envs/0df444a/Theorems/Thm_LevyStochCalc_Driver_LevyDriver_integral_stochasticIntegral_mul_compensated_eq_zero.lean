-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_stochasticIntegral_mul_compensated_eq_zero
-- name    : LevyStochCalc.Driver.LevyDriver.integral_stochasticIntegral_mul_compensated_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:22:34.038461+00:00
-- url     : https://prove2.me/theorems/196d1c72-d24d-493b-ba74-7acfe05710de
-- title:
--   integral stochasticIntegral mul compensated eq zero
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_stochasticIntegral_mul_compensated_eq_zero` is extracted from `LevyStochCalc.Driver.CrossOrthogonality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002
import Definitions.Def_LevyStochCalc_Driver_CrossSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Brownian and compensated ranges are orthogonal

Both integrals are `L²` limits of elementary ones — the Brownian integral of the master
approximants, the compensated integral of the mark-step stages — and the elementary pairings all
vanish, so the pairing of the limits vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_stochasticIntegral_mul_compensated_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d}
    (hℱW : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : Ω → ℝ → E → ℝ} (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs t ω
      * Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs t ω ∂P = 0 := by sorry
