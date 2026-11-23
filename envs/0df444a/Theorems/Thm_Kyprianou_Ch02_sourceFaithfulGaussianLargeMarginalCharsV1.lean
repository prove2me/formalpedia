-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianLargeMarginalCharsV1
-- name    : Kyprianou.Ch02.sourceFaithfulGaussianLargeMarginalCharsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:57:12.248056+00:00
-- url     : https://prove2.me/theorems/e82554fb-d802-4496-b2a4-4dcd0cc1fead
-- title:
--   Theorem 2.1 Gaussian-drift and large-Poisson marginal characteristic exponents
-- statement:
--   Given the exact Gaussian drift and Poisson large-jump component identities of Theorem 2.1, show their two source characteristic exponents for any time and Fourier parameter. The Gaussian exponent is i(-a)ξ - σ² ξ²/2. The large-jump exponent is the compensated Lévy integrand on the complement of (-1,1), including jumps of exactly magnitude 1, with no compensation term there. Use the Brownian motion Gaussian law and the Poisson random measure exponential formula, with no reliance on the compensated small-jump process.
-- source:
--   Kyprianou 2006 Theorem 2.1 Gaussian and large-jump terms, Lévy–Khintchine equation (2.5)

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

theorem sourceFaithfulGaussianLargeMarginalCharsV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (Xgauss Xlarge : ℝ≥0 → Ω → ℝ)
    (hgauss : ∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
    (hlarge : ∀ t ω, Xlarge t ω = Kyprianou.largeJumpProcess P levyMeasure N t ω) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      (charFun (P.map (Xgauss t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          (Complex.I * (((-a) * ξ : ℝ) : ℂ) -
            (((((σ ^ 2 : ℝ≥0) : ℝ) * ξ ^ 2 / 2 : ℝ)) : ℂ)))) ∧
      (charFun (P.map (Xlarge t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in (Set.Ioo (-1 : ℝ) 1)ᶜ,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))
    := by sorry

end Kyprianou.Ch02
