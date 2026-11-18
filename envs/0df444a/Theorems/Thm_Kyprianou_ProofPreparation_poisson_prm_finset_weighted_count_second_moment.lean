-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_finset_weighted_count_second_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_finset_weighted_count_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:56:29.820053+00:00
-- url     : https://prove2.me/theorems/204c8597-3535-4d82-b71a-6e38672c7515
-- title:
--   Exact second moment of finite weighted disjoint Poisson region counts
-- statement:
--   For a finite family of pairwise disjoint measurable regions of finite intensity, the second moment of the real weighted Poisson count sum equals the square of the weighted mean plus the sum of squared weights times intensities. Fully general finite simple-function count second moment, obtained from proved indexed pair-product integrability, exact diagonal and off-diagonal moments, finite weighted quadratic integral identity and finite-sum Poisson covariance algebra. Chapter 2 Theorem 2.7's finite simple-function stage.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.7, finite simple Poisson stochastic integral isometry.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_pair_count_product_integrable
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_count_pair_moment_kernel
import Theorems.Thm_Kyprianou_ProofPreparation_real_finset_weighted_square_integral
import Theorems.Thm_Kyprianou_ProofPreparation_real_finset_poisson_pair_moment_algebra
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_finset_weighted_count_second_moment
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
    (∫ ω, (∑ i ∈ F, a i *
      (ProbabilityTheory.poissonRandomMeasure K Y ω (A i)).toReal) ^ 2 ∂P) =
      (∑ i ∈ F, a i * (m (A i)).toReal) ^ 2 +
        ∑ i ∈ F, (a i) ^ 2 * (m (A i)).toReal := by sorry
end Kyprianou.ProofPreparation
