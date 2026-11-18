-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_indicator_integral_second_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_indicator_integral_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:05:23.316205+00:00
-- url     : https://prove2.me/theorems/5ff9e649-3637-44d0-b3af-5e7c3c53a2e5
-- title:
--   Raw second moment of a Poisson random-measure indicator integral
-- statement:
--   For a finite-intensity measurable region A, the real Bochner integral of its indicator against a Poisson random measure has second moment λ²+λ, with λ=m(A). This transfers the Poisson count-square law to the simplest nonnegative integrand in Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite indicator integrands.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_lintegral_sq
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_indicator_integral_second_moment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    (∫ ω, (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
      (m A).toReal ^ 2 + (m A).toReal := by sorry
end Kyprianou.ProofPreparation
