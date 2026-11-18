-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_measurable_lintegral_poissonRandomMeasure
-- name    : Kyprianou.ProofPreparation.measurable_lintegral_poissonRandomMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:17:14.235816+00:00
-- url     : https://prove2.me/theorems/6f4e67d9-d6e8-4185-a4b1-f2bc1fb0737b
-- title:
--   Measurability of nonnegative Poisson random-measure integrals
-- statement:
--   For any measurable ENNReal-valued integrand on a sigma-finite Poisson point-family mark space, the nonnegative Poisson random-measure integral is a measurable function of the sample. Derive by nonnegative simple-function approximation, measurability of Poisson random-measure evaluations, finite weighted sums and a measurable countable supremum. This provides the missing general measurability bridge for Chapter 2 Theorem 2.7 integrability and Campbell formulae.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, measurability of Poisson integrals.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem measurable_lintegral_poissonRandomMeasure
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    {g : E → ENNReal} (hg : Measurable g) :
    Measurable (fun ω => ∫⁻ x, g x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) := by sorry
end Kyprianou.ProofPreparation
