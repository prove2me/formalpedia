-- Prove2me | Theorems.Thm_Kyprianou_ch02PoissonIntegralSecondMoment
-- name    : Kyprianou.ch02PoissonIntegralSecondMoment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T21:44:07.022206+00:00
-- url     : https://prove2.me/theorems/3c9c9486-7599-413b-a32d-aa4b8a9e60d5
-- title:
--   Second-moment Poisson integral identity
-- statement:
--   Second-moment Poisson integral identity. Proper source-exact component of Kyprianou Chapter 2 Theorem 2.7, with original quantification and hypotheses.
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
theorem ch02PoissonIntegralSecondMoment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
((Integrable f m ∧ MemLp f 2 m) →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
          (∫ x, f x ^ 2 ∂m) + (∫ x, f x ∂m) ^ 2)
    := by sorry
end Kyprianou
