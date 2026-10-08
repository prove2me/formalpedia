-- Prove2me | Theorems.Thm_GenEmpLik_Consistency_lemma_13
-- name    : GenEmpLik.Consistency.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:53:23.582082+00:00
-- url     : https://prove2.me/theorems/7c4cec7b-893d-42cf-b052-970f08f754f7
-- title:
--   Lemma 13 — weights in the f-divergence ball satisfy ‖np − 𝟙‖₂ ≤ √(ρ C_f)
-- statement:
--   Let $f$ satisfy Assumption A and let $\rho\ge0$. Then there are constants $C_f\ge c_f>0$, depending only on $f$ (and $\rho$), such that
--
--   $$
--   \sqrt{\rho c_f}\ \le\ \sup_{n\in\mathbb N}\ \sup_{p\in\mathbb R^n}\Big\{\|np-\mathbb 1\|_2 \;:\; p^\top\mathbb 1=1,\ p\ge0,\ \sum_{i=1}^n f(np_i)\le\rho\Big\}\ \le\ \sqrt{\rho C_f}.
--   $$
--
--   Precisely: every $n\ge1$ and every feasible $p$ satisfy $\|np-\mathbb 1\|_2\le\sqrt{\rho C_f}$, and some $n\ge1$ and feasible $p$ satisfy $\|np-\mathbb 1\|_2\ge\sqrt{\rho c_f}$.
--
--   The lemma says that the likelihood ratios $np_i$ of every distribution in the ball $\{P\ll\widehat P_n : D_f(P\|\widehat P_n)\le\rho/n\}$ stay within a fixed $\ell_2$-distance of the all-ones vector, uniformly in $n$; it is the quantitative input to the uniform convergence in Theorem 7.
--
--   **Formalization Note** The feasible set is the published `probUncertaintySet f (1/n,…,1/n) (ρ/n)`, equal to the set displayed above. The page says "depending only on $f$"; the constants are allowed to depend on $\rho$ as well, as the proof does (it defines $m,M$ through $f(m)=f(M)=\rho$). The upper bound as proved is $\sqrt{2C_f\rho}$; the factor 2 is absorbed into the existential constant. The lower bound is stated with an attained witness, which implies the bound on the supremum. Mission 2 of this series states the same lemma in its own namespace.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 34, Lemma 13 (proof p. 35)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_GenEmpLik_Coverage_AssumptionA

namespace GenEmpLik.Consistency

/-- Lemma 13 (arXiv:1610.03425v3, p. 34): under Assumption A, for every `ρ ≥ 0` there are
constants `C_f ≥ c_f > 0` (depending only on `f` and `ρ`) such that
`√(ρ c_f) ≤ sup_n sup_p ‖n p − 𝟙‖₂ ≤ √(ρ C_f)`, the supremum running over `n ≥ 1` and
`p ∈ ℝⁿ` with `pᵀ𝟙 = 1`, `p ≥ 0`, `∑ᵢ f(n pᵢ) ≤ ρ`. The feasible set is written as the
φ-divergence ball `probUncertaintySet f (1/n, …, 1/n) (ρ/n)`; the upper bound holds for every
feasible `p`, and the lower bound is witnessed by some `n` and feasible `p`. -/
theorem lemma_13 (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ cf Cf : ℝ, 0 < cf ∧ cf ≤ Cf ∧
      (∀ n : ℕ, 0 < n → ∀ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f
          (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
        Real.sqrt (∑ i, ((n : ℝ) * p i - 1) ^ 2) ≤ Real.sqrt (ρ * Cf)) ∧
      (∃ n : ℕ, 0 < n ∧ ∃ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f
          (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
        Real.sqrt (ρ * cf) ≤ Real.sqrt (∑ i, ((n : ℝ) * p i - 1) ^ 2)) := by sorry

end GenEmpLik.Consistency
