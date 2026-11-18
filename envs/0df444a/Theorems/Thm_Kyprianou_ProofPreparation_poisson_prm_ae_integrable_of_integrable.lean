-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_ae_integrable_of_integrable
-- name    : Kyprianou.ProofPreparation.poisson_prm_ae_integrable_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:20:48.259251+00:00
-- url     : https://prove2.me/theorems/2e5b20f6-3f65-42e6-be03-4ccc329dee97
-- title:
--   Almost-sure integrability of an intensity-integrable Poisson stochastic integrand
-- statement:
--   If a real measurable function is integrable against the Poisson intensity measure, then it is Bochner integrable against the random Poisson counting measure for almost every sample. Use Campbell's proved nonnegative formula on the ENNReal norm, general measurability of the resulting random norm integral, and almost-sure finiteness from finite expected norm. This is the forward sufficiency direction of the Chapter 2 Theorem 2.7 convergence criterion and supports the raw/compensated sum bridge.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, Poisson integral absolute convergence sufficiency.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_lintegral_poissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_measurable_lintegral_poissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_ae_integrable_of_integrable
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) (hfi : Integrable f m) :
    ∀ᵐ ω ∂P, Integrable f
      (ProbabilityTheory.poissonRandomMeasure K Y ω) := by sorry
end Kyprianou.ProofPreparation
