-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_simple_integral_first_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_finset_simple_integral_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:37:57.827433+00:00
-- url     : https://prove2.me/theorems/020c8f64-e1e1-498d-bd29-a7f4f3311097
-- title:
--   Exact Campbell first moment of a signed finite-simple Poisson stochastic integral
-- statement:
--   For any finite family of finite-intensity measurable regions with real weights, the expectation of the corresponding original Poisson random-measure Bochner simple-function integral equals the intensity integral, expressed as the weighted sum of set intensities. This composes the proved finite-family a.e. pathwise integral/count identity with the proved finite weighted count first moment, retaining all quantifiers and without disjointness.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, signed finite simple-function Campbell formula.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_first_moment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_finset_simple_integral_first_moment
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E) (a : ι → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤) :
    (∫ ω, (∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
      ∑ i ∈ F, a i * (m (A i)).toReal := by sorry
end Kyprianou.ProofPreparation
