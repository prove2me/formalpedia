-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkedHorizonIntegrand_integral_mean_zero
-- name    : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mean_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:26:45.876279+00:00
-- url     : https://prove2.me/theorems/93ef91ba-12d1-4710-bb32-75e2f69911d6
-- title:
--   integral mean zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mean_zero` is extracted from `LevyStochCalc.Poisson.CompensatedRange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Progressive

namespace MarkedHorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mean_zero (hT : 0 ≤ T) (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∫ ω, G.integral N hℱ ω ∂P = 0 := by sorry
