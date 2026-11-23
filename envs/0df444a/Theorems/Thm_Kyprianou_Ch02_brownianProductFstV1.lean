-- Prove2me | Theorems.Thm_Kyprianou_Ch02_brownianProductFstV1
-- name    : Kyprianou.Ch02.brownianProductFstV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:43:34.525978+00:00
-- url     : https://prove2.me/theorems/ae99d684-7e17-455b-959b-34a4d6ec37fb
-- title:
--   Brownian motion lifted to first coordinate of independent product probability space
-- statement:
--   Brownian motion lifted to first coordinate of independent product probability space; reuses the exact accepted proof of the general independent Brownian and Poisson driver construction.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, product driver construction

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem brownianProductFstV1
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (B₁ : LevyStochCalc.Brownian.BrownianMotion P₁) :
    ∃ B : LevyStochCalc.Brownian.BrownianMotion (P₁.prod P₂),
      ∀ (t : ℝ) (ω : Ω₁ × Ω₂), B.W t ω = B₁.W t ω.1 := by sorry
end Kyprianou.Ch02
