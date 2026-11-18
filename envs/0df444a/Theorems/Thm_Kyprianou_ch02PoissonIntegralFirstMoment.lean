-- Prove2me | Theorems.Thm_Kyprianou_ch02PoissonIntegralFirstMoment
-- name    : Kyprianou.ch02PoissonIntegralFirstMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:44:11.446199+00:00
-- url     : https://prove2.me/theorems/72a18ae8-c213-4c5a-bca3-bc4d54e64b25
-- title:
--   Campbell expectation identity for integrable Poisson random measure functions
-- statement:
--   Campbell expectation identity for integrable Poisson random measure functions. Proper source-exact component of Kyprianou Chapter 2 Theorem 2.7, with original quantification and hypotheses.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem ch02PoissonIntegralFirstMoment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
(Integrable f m →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
        ∫ x, f x ∂m)    := by sorry
end Kyprianou
