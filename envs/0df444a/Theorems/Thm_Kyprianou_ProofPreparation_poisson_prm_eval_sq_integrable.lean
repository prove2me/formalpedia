-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_sq_integrable
-- name    : Kyprianou.ProofPreparation.poisson_prm_eval_sq_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:13:07.536735+00:00
-- url     : https://prove2.me/theorems/6dfde0de-4d7a-4b91-b9e6-ee4de1c25c1b
-- title:
--   Square integrability of Poisson count evaluations on finite-intensity sets
-- statement:
--   A finite-intensity measurable-region count of the original Poisson point-family random measure has an integrable squared real count, as a direct consequence of the proved finite ENNReal square mean and Mathlib's nonnegative-integral integrability criterion. Needed to justify termwise expectation in the two-cell simple-function second moment.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, simple-function second-moment integrability.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_lintegral_sq
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_eval_sq_integrable
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Integrable (fun ω => ((ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal) ^ 2) P := by sorry
end Kyprianou.ProofPreparation
