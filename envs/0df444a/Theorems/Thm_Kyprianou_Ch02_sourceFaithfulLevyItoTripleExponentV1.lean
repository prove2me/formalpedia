-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoTripleExponentV1
-- name    : Kyprianou.Ch02.sourceFaithfulLevyItoTripleExponentV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:36:55.58172+00:00
-- url     : https://prove2.me/theorems/143e8311-0ba1-41b9-b62f-cd9791279b1c
-- title:
--   Theorem 2.1: characteristic exponent of the independent Gaussian, large-jump and compensated-small-jump sum
-- statement:
--   Given Brownian motion, Poisson random measure, the exact Gaussian drift and large-jump physical component identities, the small-jump characteristic exponent and mutual independence of all three paths, prove the Lévy–Khintchine characteristic exponent of their sum. Requires the Gaussian law, Poisson exponential formula, factorisation of independent characteristic functions and the precise truncation convention. No independent construction theorem is assumed.
-- source:
--   Kyprianou (2006), Theorem 2.1 and Lévy–Khintchine Eq (2.5), Chapter 2

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

theorem sourceFaithfulLevyItoTripleExponentV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : ∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
    (hlarge : ∀ t ω, Xlarge t ω = Kyprianou.largeJumpProcess P levyMeasure N t ω)
    (hsmall : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (Xsmall t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioo (-1 : ℝ) 1,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        Kyprianou.Ch01.levyTripleExponent
          ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ) := by sorry

end Kyprianou.Ch02
