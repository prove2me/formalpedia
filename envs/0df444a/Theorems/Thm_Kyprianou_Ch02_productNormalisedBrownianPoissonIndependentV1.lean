-- Prove2me | Theorems.Thm_Kyprianou_Ch02_productNormalisedBrownianPoissonIndependentV1
-- name    : Kyprianou.Ch02.productNormalisedBrownianPoissonIndependentV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T21:35:58.503862+00:00
-- url     : https://prove2.me/theorems/bd8bc9d4-58ba-42cb-8cfd-a7103df13535
-- title:
--   Independent product-space Brownian and Poisson drivers with pointwise zero start
-- statement:
--   Lift a given BrownianMotion and PoissonRandomMeasure from two independent probability spaces to their product probability space, preserving Brownian and Poisson laws, full path independence, and the pointwise Brownian zero-start certificate.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, independent-driver construction

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem productNormalisedBrownianPoissonIndependentV1
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (ν : Measure ℝ) [SigmaFinite ν]
    (B₁ : LevyStochCalc.Brownian.BrownianMotion P₁)
    (N₂ : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P₂ ν)
    (hB₁zero : ∀ ω : Ω₁, B₁.W 0 ω = 0) :
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion (P₁.prod P₂))
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} (P₁.prod P₂) ν),
      ProbabilityTheory.IndepFun
        (fun ω => fun (t : ℝ) => B.W t ω)
        (fun ω => N.N ω) (P₁.prod P₂) ∧
      (∀ ω : Ω₁ × Ω₂, B.W 0 ω = 0) := by sorry
end Kyprianou.Ch02
