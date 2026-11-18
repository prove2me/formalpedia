-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_count_centered_isometry
-- name    : Kyprianou.ProofPreparation.poisson_prm_finset_count_centered_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:21:56.689781+00:00
-- url     : https://prove2.me/theorems/c19f6e18-5a98-40ae-ac01-a86369420695
-- title:
--   Centred L2 isometry of finite weighted disjoint Poisson region counts
-- statement:
--   For finite disjoint measurable finite-intensity Poisson cells, the expectation of the squared centred weighted region-count sum is exactly the intensity weighted sum of coefficient squares. Source-faithful finite-simple compensated Poisson isometry obtained from accepted pair-product integrability, first and second moments and deterministic square centring. Precursor for Chapter 2 Theorem 2.7 full compensated Poisson L² extension.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, centred finite simple Poisson variance.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_pair_count_product_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_first_moment
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_second_moment
import Theorems.Thm_Kyprianou_ProofPreparation_real_finset_weighted_square_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_real_centered_square_integral
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_finset_count_centered_isometry
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
    (∫ ω, ((∑ i ∈ F, a i *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal) -
      ∑ i ∈ F, a i * (m (A i)).toReal) ^ 2 ∂P) =
      ∑ i ∈ F, a i ^ 2 * (m (A i)).toReal := by sorry
end Kyprianou.ProofPreparation
