-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_exists_markedPredictable_markedHorizonIntegrand
-- name    : LevyStochCalc.Poisson.Compensated.exists_markedPredictable_markedHorizonIntegrand
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:44:31.664858+00:00
-- url     : https://prove2.me/theorems/e4591240-5a94-45a7-9c65-d18a7cfffccb
-- title:
--   exists markedPredictable markedHorizonIntegrand
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.exists_markedPredictable_markedHorizonIntegrand` is extracted from `LevyStochCalc.Poisson.PredictableIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PredictableIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissible marked integrands have predictable versions

An admissible marked integrand agrees almost everywhere with a predictable process; cutting that
process to the horizon keeps it predictable — the horizon strip is a countable union of windows
of finite mark measure — and makes it admissible, and the two compensated integrals agree almost
surely because the energy of their difference vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Probability

theorem _root_.LevyStochCalc.Poisson.Compensated.exists_markedPredictable_markedHorizonIntegrand
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∃ G' : MarkedHorizonIntegrand P ν ℱ T, MarkedPredictable ℱ ν G'.toFun ∧
      G'.integral N hℱ =ᵐ[P] G.integral N hℱ := by sorry
