-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_exists_markedHorizonIntegrand_of_mean_zero
-- name    : LevyStochCalc.Poisson.Compensated.exists_markedHorizonIntegrand_of_mean_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:31:58.709041+00:00
-- url     : https://prove2.me/theorems/a98a2b2b-d11f-4404-b296-50c30fd2e34b
-- title:
--   exists markedHorizonIntegrand of mean zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.exists_markedHorizonIntegrand_of_mean_zero` is extracted from `LevyStochCalc.Poisson.CompensatedRange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003

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

end Integral

end MarkedHorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

theorem _root_.LevyStochCalc.Poisson.Compensated.exists_markedHorizonIntegrand_of_mean_zero (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P →
      (∫ ω, r ω ∂P = 0) →
      (∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, r ω * G.integral N hℱ ω ∂P = 0) → r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : MarkedHorizonIntegrand P ν ℱ T, Z =ᵐ[P] G.integral N hℱ := by sorry
