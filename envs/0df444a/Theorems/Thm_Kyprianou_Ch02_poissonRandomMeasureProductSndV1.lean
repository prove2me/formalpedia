-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonRandomMeasureProductSndV1
-- name    : Kyprianou.Ch02.poissonRandomMeasureProductSndV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T21:43:26.132149+00:00
-- url     : https://prove2.me/theorems/a97fdcf9-2dfc-410d-bf66-8eed9aca7fd8
-- title:
--   Poisson random measure lifted to second coordinate of independent product probability space
-- statement:
--   Poisson random measure lifted to second coordinate of independent product probability space; reuses the exact accepted proof of the general independent Brownian and Poisson driver construction.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, product driver construction

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem poissonRandomMeasureProductSndV1
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N₂ : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P₂ ν) :
    ∃ N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} (P₁.prod P₂) ν,
      ∀ ω : Ω₁ × Ω₂, N.N ω = N₂.N ω.2 := by sorry
end Kyprianou.Ch02
