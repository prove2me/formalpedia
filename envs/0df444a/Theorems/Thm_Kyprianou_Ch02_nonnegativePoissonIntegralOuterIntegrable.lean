-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativePoissonIntegralOuterIntegrable
-- name    : Kyprianou.Ch02.nonnegativePoissonIntegralOuterIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:26:33.362756+00:00
-- url     : https://prove2.me/theorems/f64b2bb0-729d-4137-b5f6-d1c040cce12f
-- title:
--   Bochner integrability of nonnegative Poisson integrals under finite intensity mean
-- statement:
--   A nonnegative intensity-integrable function has an integrable random Poisson integral. Derived from the source-faithful nonnegative Campbell identity for Kyprianou (2006) Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.7 pp. 41–43, Bochner integrability of the Poisson sum.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_lintegral_poissonRandomMeasure
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem nonnegativePoissonIntegralOuterIntegrable
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hfi : Integrable f m) :
    Integrable
      (fun ω => ∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) P := by sorry
end Kyprianou.Ch02
