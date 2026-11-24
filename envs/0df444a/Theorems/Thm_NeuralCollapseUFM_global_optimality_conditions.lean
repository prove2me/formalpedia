-- Prove2me | Theorems.Thm_NeuralCollapseUFM_global_optimality_conditions
-- name    : NeuralCollapseUFM.global_optimality_conditions
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:18:22.564451+00:00
-- url     : https://prove2.me/theorems/f2b2a674-72c8-4b70-9e54-dc4ef8aa2050
-- title:
--   Theorem 3.1 (as proved): global minimizers are Simplex ETFs (Neural Collapse)
-- statement:
--   Let $K\ge2$ classes with $n\ge1$ samples each, feature dimension $d\ge K$, $\lambda_W,\lambda_H>0$ and $\lambda_b\ge0$. Let $(W^\star,H^\star,b^\star)$ be a global minimizer of the objective $f$ in (4). Then there are $w^\star,b^\star\in\mathbb{R}$ such that
--
--   1. $\|w^{\star1}\|_2=\cdots=\|w^{\star K}\|_2=w^\star$;
--   2. $b^\star=b^\star1$, where $b^\star=0$ or $\lambda_b=0$;
--   3. $h^\star_{k,i}=\sqrt{\frac{\lambda_W}{\lambda_Hn}}\,w^{\star k}$ for all $k\in[K]$, $i\in[n]$, and $\bar h^\star_i=\frac1K\sum_{j=1}^Kh^\star_{j,i}=0$ for all $i\in[n]$;
--   4. the classifier forms a Simplex ETF up to scaling:
--
--   $$W^\star W^{\star\top}=(w^\star)^2\,\frac{K}{K-1}\Big(I_K-\frac1K1_K1_K^\top\Big).$$
--
--   This is Neural Collapse for the regularized unconstrained feature model: within-class variability vanishes, and the class features and classifiers align with a Simplex ETF.
--
--   **Formalization Note** The paper normalizes by $1/w^\star$ and states $M^\top M=\frac{K}{K-1}(I_K-\frac1K1_K1_K^\top)$ for $M=\frac1{w^\star}UW^{\star\top}$, $U$ orthogonal. Since $M^\top M=W^\star W^{\star\top}/(w^\star)^2$, this is item 4 divided by $(w^\star)^2$. The proof establishes item 4 as written. The printed normalization is undefined when $w^\star=0$, and $(W,H,b)=(0,0,0)$ is a global minimizer when $K^2n\lambda_W\lambda_H\ge1$ (the unique one when $K^2n\lambda_W\lambda_H>1$). The main text assumes $d\ge K$ and Appendix B assumes $d>K$; the main-text hypothesis is used. The case $\lambda_b=0$ is included because the theorem's conclusion mentions it.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Section 3.1, Theorem 3.1, eqs. (5)-(6), p. 9; restated as Theorem B.1, p. 30, proof pp. 30-31

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem global_optimality_conditions {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n) (hd : K ≤ d)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 ≤ lamb)
    (x : Params K d n) (hx : IsGlobalMinimizer (objective lamW lamH lamb) x) :
    IsCollapsedSolution lamW lamH lamb x := by sorry

end NeuralCollapseUFM
