-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_lemma_13
-- name    : GenEmpLik.Coverage.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:27:09.159736+00:00
-- url     : https://prove2.me/theorems/e4e02fd4-d5c6-4800-890b-48ca34b757df
-- title:
--   Lemma 13 — divergence-ball weights stay near uniform
-- statement:
--   Let $f$ satisfy Assumption A and fix $\rho>0$. There are constants $0<c_{f,\rho}\le C_{f,\rho}$ such that every feasible weight vector $p$ at every positive sample size satisfies
--
--   $$\left\|np-\mathbf1\right\|_2\le\sqrt{\rho C_{f,\rho}},$$
--
--   and at some positive sample size a feasible vector satisfies $\sqrt{\rho c_{f,\rho}}\le\|np-\mathbf1\|_2$. Thus the supremum over all sample sizes and feasible weights lies between these two bounds.
--
--   **Formalization Note** The proof on p. 35 chooses truncation points using $\rho$, so the constants may depend on both $f$ and $\rho$. Its factor of $2$ is absorbed into the existential constants.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 34, Lemma 13; proof p. 35

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_divergenceBall

namespace GenEmpLik.Coverage

/-- Lemma 13, p. 34, with constants allowed to depend on f and ρ, as in its proof. -/
theorem lemma_13 (f : ℝ → EReal) (hA : AssumptionA f)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ cf Cf : ℝ, 0 < cf ∧ cf ≤ Cf ∧
      (∀ n : ℕ, 0 < n → ∀ p ∈ divergenceBall f ρ n,
        Real.sqrt (∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2) ≤ Real.sqrt (ρ * Cf)) ∧
      (∃ n : ℕ, 0 < n ∧ ∃ p ∈ divergenceBall f ρ n,
        Real.sqrt (ρ * cf) ≤ Real.sqrt (∑ i : Fin n, ((n : ℝ) * p i - 1) ^ 2)) := by sorry

end GenEmpLik.Coverage
