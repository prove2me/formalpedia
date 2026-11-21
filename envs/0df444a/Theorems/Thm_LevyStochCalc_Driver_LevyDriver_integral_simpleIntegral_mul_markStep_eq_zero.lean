-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_simpleIntegral_mul_markStep_eq_zero
-- name    : LevyStochCalc.Driver.LevyDriver.integral_simpleIntegral_mul_markStep_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:21:06.557519+00:00
-- url     : https://prove2.me/theorems/3b25f513-4b97-4857-a20c-452f760bd958
-- title:
--   integral simpleIntegral mul markStep eq zero
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_simpleIntegral_mul_markStep_eq_zero` is extracted from `LevyStochCalc.Driver.CrossSimple`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CrossSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Elementary integrals against the two drivers are orthogonal

An elementary Brownian integral and the compensated integral of a mark-step integrand expand
into finite sums of cross terms, one for each pair of cells. Clamping a cell to a running time
either collapses it, killing the term, or leaves its left endpoint alone, where the coefficient
is measurable; so every term has zero mean and the pairing vanishes at any pair of times.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open Brownian.Multidim.MultidimBrownianMotion (min_eq_or_lt_min)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_simpleIntegral_mul_markStep_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d}
    {TH : ℝ} (H : Brownian.Ito.SimplePredictable Ω TH)
    (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
    {g : Poisson.Compensated.TimeGrid} (G : Poisson.Compensated.MarkStep Ω E ν g)
    (hG : G.Adapted ℱ) (t t' : ℝ) :
    ∫ ω, Brownian.Ito.simpleIntegral (D.W.W i) H t ω * G.integral D.N t' ω ∂P = 0 := by sorry
