-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftCharFunV1
-- name    : Kyprianou.Ch02.sourceFaithfulGaussianDriftCharFunV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:57:05.693653+00:00
-- url     : https://prove2.me/theorems/e2a5eadb-5b15-4c83-a6b5-744f73d3cb2c
-- title:
--   Brownian Gaussian component with negative drift has the source-faithful Fourier exponent
-- statement:
--   The Gaussian component Xgauss(t)=σ W(t)−a t of a standard Brownian motion has characteristic function exp(t(-i a ξ - σ² ξ²/2)). Use KLS Brownian marginal law and existing Chapter 1 Gaussian characteristic function identities, along with deterministic translation of characteristic functions.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1: characteristic exponent of the three Lévy–Itô components.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem sourceFaithfulGaussianDriftCharFunV1
    (a : ℝ) (σ : ℝ≥0)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (Xgauss : ℝ≥0 → Ω → ℝ)
    (hgauss : ∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (Xgauss t)) ξ = Complex.exp ((((t : ℝ) : ℂ)) *
          (-Complex.I * (a : ℂ) * (ξ : ℂ) -
            (((σ : ℝ) ^ 2 * ξ ^ 2 / 2 : ℝ) : ℂ))) := by sorry

end Kyprianou.Ch02
