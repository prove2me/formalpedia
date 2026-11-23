-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_theorem1_binomial_quantile_bound
-- name    : GeneralAgentsWorldModels.theorem1_binomial_quantile_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:39:00.347245+00:00
-- url     : https://prove2.me/theorems/4d6db3a5-e496-4d61-beef-5588f84db049
-- title:
--   Theorem 1 (proof, eqs. (41)-(42), (54)-(56)): a relaxed median of $\mathrm{Bin}(m,p)$ is close to $mp$
-- statement:
--   Let $X\sim\mathrm{Bin}(m,p)$ with $0\le p\le1$, let $0\le\delta<1$, and let $k\in\mathbb N$ satisfy the relaxed median conditions (41)-(42):
--
--   $$P_m(X\le k)\ge\frac{1-\delta}{2-\delta},\qquad P_m(X\ge k)\ge\frac{1-\delta}{2-\delta}.$$
--
--   Then
--
--   $$|k-mp|\le\sqrt{\frac{mp(1-p)}{1-\delta}}.$$
--
--   This is the step from the agent's goal-switching point $k^*$ to the error of the estimate $\hat P_{ss'}(a)=k^*/m$.
--
--   **Formalization Note** The paper derives (56) from (42) and the one-sided Chebyshev inequality (54), which bounds $k-mp$ from above; the bound on $mp-k$ uses (41) and the lower one-sided Chebyshev inequality in the same way. Both directions are stated.
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Appendix A.6, proof of Theorem 1, eqs. (41), (42), (54)-(56), pp. 19-20

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem theorem1_binomial_quantile_bound (m : ℕ) (p δ : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (k : ℕ)
    (hle : (1 - δ) / (2 - δ) ≤ binLE m p k) (hge : (1 - δ) / (2 - δ) ≤ binGE m p k) :
    |(k : ℝ) - m * p| ≤ Real.sqrt (m * p * (1 - p) / (1 - δ)) := by sorry

end GeneralAgentsWorldModels
