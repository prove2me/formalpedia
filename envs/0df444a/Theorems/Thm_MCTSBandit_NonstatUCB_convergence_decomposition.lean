-- Prove2me | Theorems.Thm_MCTSBandit_NonstatUCB_convergence_decomposition
-- name    : MCTSBandit.NonstatUCB.convergence_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:54.876893+00:00
-- url     : https://prove2.me/theorems/9892c32c-849c-49b1-8586-b311eaa12f5e
-- title:
--   Convergence decomposition — loss through suboptimal plays
-- statement:
--   Let $\bar X_n$ be the average reward of any measurable arm-selection run, and let $i_*$ designate an arm. Bounded rewards give
--
--   $$\left|\mu_*-\mathbb E[\bar X_n]\right|\le\left|\mathbb E[\bar X_{i_*,n}]-\mu_*\right|+\frac{2R}{n}\mathbb E\!\left[\sum_{i\ne i_*}T_i(n)\right],\qquad n\ge1.$$
--
--   The estimate separates the optimal arm's mean bias from the cost of plays assigned elsewhere.
--
--   **Formalization Note** The printed middle equality on p. 18 is interpreted as the triangle inequality. This bound holds for every measurable run, so the UCB rule is not required.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, p. 18, §6, Completing Proof of Convergence

import Definitions.Def_MCTSBandit_NonstatUCB_UCB

open MeasureTheory

namespace MCTSBandit.NonstatUCB

universe u

/-- Shah–Xie–Xu, completing the proof of convergence, p. 18. -/
theorem convergence_decomposition {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (istar : Fin K)
    (I : ℕ → Ω → Fin K) (R β ξ η : ℝ)
    (hR : 0 < R) (hβ : 1 < β) (hξ : 0 < ξ)
    (hη0 : (1 / 2 : ℝ) ≤ η) (hη1 : η < 1)
    (hM : IsNonstatMAB P X μ R β ξ η)
    (hIm : RunMeasurable I) :
    ∀ n : ℕ, 1 ≤ n →
      |μ istar - ∫ ω, runAvg X I n ω ∂P| ≤
        |(∫ ω, empMean X istar n ω ∂P) - μ istar| +
        2 * R *
          (∫ ω, (∑ i ∈ (Finset.univ : Finset (Fin K)).erase istar,
            (pullCount I i n ω : ℝ)) ∂P) / (n : ℝ) := by sorry

end MCTSBandit.NonstatUCB
