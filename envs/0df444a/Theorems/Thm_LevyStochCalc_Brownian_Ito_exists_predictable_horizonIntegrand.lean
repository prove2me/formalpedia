-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_predictable_horizonIntegrand
-- name    : LevyStochCalc.Brownian.Ito.exists_predictable_horizonIntegrand
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:53:58.293762+00:00
-- url     : https://prove2.me/theorems/9ef3e9e3-8262-40ed-9e57-dca9f0e06940
-- title:
--   exists predictable horizonIntegrand
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_predictable_horizonIntegrand` is extracted from `LevyStochCalc.Brownian.PredictableIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PredictableIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissible integrands have predictable versions

An admissible integrand agrees almost everywhere with a predictable process; cutting that process
to the horizon keeps it predictable and makes it admissible, and the two integrals agree almost
surely because the energy of their difference vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Probability

theorem _root_.LevyStochCalc.Brownian.Ito.exists_predictable_horizonIntegrand (W : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration W ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) {T : ℝ} (hT : 0 < T)
    (G : HorizonIntegrand P ℱ T) :
    ∃ G' : HorizonIntegrand P ℱ T, Predictable ℱ G'.toFun ∧
      G'.integral W hℱ =ᵐ[P] G.integral W hℱ := by sorry
