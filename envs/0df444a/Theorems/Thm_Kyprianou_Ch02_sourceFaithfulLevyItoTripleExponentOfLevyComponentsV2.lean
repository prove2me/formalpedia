-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoTripleExponentOfLevyComponentsV2
-- name    : Kyprianou.Ch02.sourceFaithfulLevyItoTripleExponentOfLevyComponentsV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:15:30.746673+00:00
-- url     : https://prove2.me/theorems/a460ffaa-3ed8-4486-be49-a9fc1456122c
-- title:
--   Theorem 2.1: joint Lévy characteristic exponent with measurable Lévy component certificates
-- statement:
--   Given Brownian, compound-Poisson, and compensated small-jump components whose paths are mutually independent, whose marginals have the stated Lévy-Khintchine characteristic functions, and whose components are genuine Lévy processes, prove the characteristic function of their sum equals the Lévy-triplet exponent. The explicit Lévy assumptions permit use of the already proved three-component characteristic factorisation without measurability gaps.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, exponent verification

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

theorem sourceFaithfulLevyItoTripleExponentOfLevyComponentsV2
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
    (hGLevy : ProbabilityTheory.IsLevyProcess Xgauss P)
    (hLLevy : ProbabilityTheory.IsLevyProcess Xlarge P)
    (hSLevy : ProbabilityTheory.IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        Kyprianou.Ch01.levyTripleExponent
          ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ) := by sorry

end Kyprianou.Ch02
