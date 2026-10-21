-- Prove2me | Theorems.Thm_ModernOnlineLearning_ParameterFree_wealth_dominates_potential
-- name    : ModernOnlineLearning.ParameterFree.wealth_dominates_potential
-- status  : Proved
-- author  : @suzukasan
-- created : 2026-10-21T05:37:07.761013+00:00
-- url     : https://prove2.me/theorems/624bd351-a4e6-4f72-b010-2bafba67647d
-- title:
--   Theorem 13.4, pp. 210–211: KT wealth dominates its potential
-- statement:
--   Let $\varepsilon>0$, let $T\ge0$ be an integer, and let $c_1,\ldots,c_T\in[-1,1]$. Write $S_t=\sum_{j=1}^t c_j$ and define the KT wealth by $W_T=\varepsilon\prod_{t=1}^T(1+c_t S_{t-1}/t)$. For the gamma-function potential
--
--   $$F_T(z)=\frac{\varepsilon 2^T\Gamma((T+1+z)/2)\Gamma((T+1-z)/2)}{\pi\Gamma(T+1)},$$
--
--   we have
--
--   $$F_T(S_T)\le W_T.$$
--
--   This is the wealth-domination step in Theorem 13.4, which combines with a lower bound on the potential to obtain an exponential wealth guarantee.
--
--   **Formalization Note** The statement includes the zero-round base case explicitly used in the source proof. It uses the existing definitions of KT wealth and potential.
-- source:
--   Francesco Orabona, Online Learning: A Modern Introduction Using Convex Optimization, arXiv:1912.13213v10, proof of Theorem 13.4, printed pp. 210–211. https://arxiv.org/abs/1912.13213v10

import Definitions.Def_ModernOnlineLearning_ParameterFree_Defs
open ModernOnlineLearning.ParameterFree

theorem ModernOnlineLearning.ParameterFree.wealth_dominates_potential (ε : ℝ) (hε : 0 < ε) (T : ℕ)
    (c : ℕ → ℝ) (hc : ∀ t ∈ Finset.Icc 1 T, -1 ≤ c t ∧ c t ≤ 1) :
    ktPotential ε T (∑ t ∈ Finset.Icc 1 T, c t) ≤ ktWealth ε c T := by sorry
