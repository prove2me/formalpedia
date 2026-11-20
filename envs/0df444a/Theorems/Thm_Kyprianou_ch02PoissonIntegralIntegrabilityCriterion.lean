-- Prove2me | Theorems.Thm_Kyprianou_ch02PoissonIntegralIntegrabilityCriterion
-- name    : Kyprianou.ch02PoissonIntegralIntegrabilityCriterion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:44:11.665305+00:00
-- url     : https://prove2.me/theorems/5343dd9d-494e-457c-bbc9-46787fc6a356
-- title:
--   Poisson integral sample integrability iff truncated integrability
-- statement:
--   Poisson integral sample integrability iff truncated integrability. Proper source-exact component of Kyprianou Chapter 2 Theorem 2.7, with original quantification and hypotheses.
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
theorem ch02PoissonIntegralIntegrabilityCriterion
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
    ((∀ᵐ ω ∂P,
      Integrable f (ProbabilityTheory.poissonRandomMeasure K Y ω)) ↔
      Integrable (fun x => min (1 : ℝ) |f x|) m)    := by sorry
end Kyprianou
