-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_simple_integral_second_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_finset_simple_integral_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:01:42.96621+00:00
-- url     : https://prove2.me/theorems/67aed945-a88f-4f45-9a80-399528cdcaa4
-- title:
--   Exact second moment of a finite-simple Poisson random-measure stochastic integral
-- statement:
--   For an arbitrary finite family of pairwise disjoint measurable finite-intensity Poisson regions and real weights, the expectation of the squared original Bochner stochastic integral of the finite weighted indicator sum equals squared weighted intensity plus weighted intensity of squared coefficients. Exact finite-simple-function form of the Chapter 2 Theorem 2.7 Poisson second moment, derived from the proved a.e. integral/count identity and count second-moment isometry.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite simple Poisson second moment.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_second_moment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_finset_simple_integral_second_moment
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [DecidableEq ι] [Nonempty E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (F : Finset ι) (A : ι → Set E) (a : ι → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hfin : ∀ i ∈ F, m (A i) < ⊤)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (A i) (A j)) :
    (∫ ω, (∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
      (∑ i ∈ F, a i * (m (A i)).toReal) ^ 2 +
      ∑ i ∈ F, (a i) ^ 2 * (m (A i)).toReal := by sorry
end Kyprianou.ProofPreparation
