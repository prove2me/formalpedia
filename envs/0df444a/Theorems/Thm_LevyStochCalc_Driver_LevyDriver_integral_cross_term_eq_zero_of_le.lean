-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_integral_cross_term_eq_zero_of_le
-- name    : LevyStochCalc.Driver.LevyDriver.integral_cross_term_eq_zero_of_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:39:00.000949+00:00
-- url     : https://prove2.me/theorems/bcf1a2e9-78fe-4899-8f61-00011b8f2917
-- title:
--   integral cross term eq zero of le
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.integral_cross_term_eq_zero_of_le` is extracted from `LevyStochCalc.Driver.CrossElementary`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One cross term between the two drivers

A Brownian increment weighted at its left endpoint, against a compensated mass weighted at its
left endpoint, has zero mean: whichever of the two cells starts later, its increment is centred
given an enlargement of the filtration carrying the whole path of the other driver, and the
remaining factor is measurable there.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

section CrossTerm

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Driver.LevyDriver.integral_cross_term_eq_zero_of_le (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ) {Mξ : ℝ}
    (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η) {Mη : ℝ}
    (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) ∂P = 0 := by sorry
