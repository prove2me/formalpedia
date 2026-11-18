-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativePoissonIntegralFirstMoment
-- name    : Kyprianou.Ch02.nonnegativePoissonIntegralFirstMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:24:42.529308+00:00
-- url     : https://prove2.me/theorems/41484a0c-7a36-4796-b725-bdff8c5e2e82
-- title:
--   Nonnegative Campbell identity and sample-integrability for Poisson random measures
-- statement:
--   For a nonnegative measurable integrable f, the Poisson point-family integral is almost surely integrable and its mean equals the intensity integral. This is the nonnegative source-faithful ingredient of Kyprianou (2006) Chapter 2 Theorem 2.7 first-moment formula, following the proved nonnegative Campbell identity.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7 pp. 41–43, nonnegative Campbell proof stage.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_lintegral_poissonRandomMeasure
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem nonnegativePoissonIntegralFirstMoment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hfi : Integrable f m) :
    (∀ᵐ ω ∂P, Integrable f
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∧
    (∫ ω, (∫ x, f x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
      ∫ x, f x ∂m := by sorry
end Kyprianou.Ch02
