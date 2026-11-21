-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_integral_mul_setIntegral_jump
-- name    : LevyStochCalc.Driver.integral_mul_setIntegral_jump
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:15:52.727193+00:00
-- url     : https://prove2.me/theorems/6d8fb180-31ba-444c-bd6f-81de678b9025
-- title:
--   integral mul setIntegral jump
-- statement:
--   The source theorem `LevyStochCalc.Driver.integral_mul_setIntegral_jump` is extracted from `LevyStochCalc.Driver.CellFubini`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellFubini_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Swapping the pairing with the time and window integrals

The two surviving terms of the paired cell identity are an integral over the sample space of a
set integral: over a time interval for the drift, over a window of times and marks for the
compensator. Both are instances of `LevyStochCalc.Probability.integral_mul_setIntegral_swap`,
which lives in the measure-theoretic layer; only the instantiations are here.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Probability
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Cell

variable {E : Type v} [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {W : LevyStochCalc.Brownian.BrownianMotion P} {hℱW : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}
  {Z : Ω → ℝ} {V : Ω → ℝ} {Mv : ℝ}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Driver.integral_mul_setIntegral_jump
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {A : Set E} (hAν : ν A ≠ ⊤)
    {K : Ω → ℝ → E → ℝ} (hKm : Measurable fun p : Ω × ℝ × E => K p.1 p.2.1 p.2.2)
    {MK : ℝ} (hKb : ∀ ω s e, |K ω s e| ≤ MK)
    (hZ1 : Integrable Z P) (hVm : AEStronglyMeasurable V P) (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (t : ℝ) :
    ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        g (l * X q.1 ω) * K ω q.1 q.2 ∂(referenceIntensity ν)) ∂P
      = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, ∫ ω, Z ω * V ω *
          (g (l * X q.1 ω) * K ω q.1 q.2) ∂P ∂(referenceIntensity ν) := by sorry
