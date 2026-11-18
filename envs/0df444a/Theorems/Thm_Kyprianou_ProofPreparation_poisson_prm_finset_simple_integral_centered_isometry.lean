-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_simple_integral_centered_isometry
-- name    : Kyprianou.ProofPreparation.poisson_prm_finset_simple_integral_centered_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:32:56.943307+00:00
-- url     : https://prove2.me/theorems/1b58a319-55a7-448c-a6cc-619a1e132e3c
-- title:
--   Exact centred L2 isometry for a finite-simple Poisson stochastic integral
-- statement:
--   For a finite signed simple function whose measurable finite-intensity supports are pairwise disjoint, the squared centred original Poisson random-measure stochastic integral has expectation equal to the intensity integral of squared coefficients. This converts the proved finite weighted-count centred isometry into the original integral via the proved a.e. finite-simple integral/count identity, a prerequisite for extension to arbitrary L² integrands in Kyprianou Chapter 2 Theorem 2.7.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, finite simple compensated Poisson L² isometry.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_count_centered_isometry
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_finset_simple_integral_centered_isometry
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
    (∫ ω, ((∫ x, (∑ i ∈ F, a i *
      (A i).indicator (fun _ => (1 : ℝ)) x) ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) -
        ∑ i ∈ F, a i * (m (A i)).toReal) ^ 2 ∂P) =
      ∑ i ∈ F, a i ^ 2 * (m (A i)).toReal := by sorry
end Kyprianou.ProofPreparation
