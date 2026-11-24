-- Prove2me | Theorems.Thm_NeuralCollapseCE_symmetric_minimizers_are_simplex_etf
-- name    : NeuralCollapseCE.symmetric_minimizers_are_simplex_etf
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:10:27.995539+00:00
-- url     : https://prove2.me/theorems/dbf18df3-34fb-47cd-91bf-01751a27ca20
-- title:
--   Theorem 2: the minimisers of the symmetric loss are the simplex ETFs
-- statement:
--   Let $n\ge2$, $d\ge n-1$ and $\alpha>0$. Consider the problem of minimising
--
--   $$\mathcal{L}_\alpha(u)=\sum_{i=1}^n\log\Big(1+\sum_{j\ne i}e^{\alpha(\langle u_j,u_i\rangle-1)}\Big)$$
--
--   over $u_1,\dots,u_n\in\mathbb{R}^d$ with $\|u_i\|=1$. A configuration $u$ is a global minimiser if and only if $\{u_i\}_{i=1}^n$ is a simplex equiangular tight frame, i.e. $\langle u_i,u_j\rangle=-\frac1{n-1}$ for all $i\ne j$.
--
--   This is the symmetric version ($v_i=\alpha u_i$) of the cross-entropy problem of Theorem 1.
--
--   **Formalization Note** "The global minimum corresponds to the simplex ETF" is stated as an equivalence between being a constrained global minimiser and being a simplex ETF. The paper assumes $n\ge2$ implicitly (it divides by $n-1$); this is written as a hypothesis.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 1.2, Theorem 2, eq. (1), p. 2; proof in Section 2, pp. 5-6

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory Filter Topology Asymptotics

namespace NeuralCollapseCE

theorem symmetric_minimizers_are_simplex_etf {n d : ℕ} (hn : 2 ≤ n) (hd : n ≤ d + 1)
    (α : ℝ) (hα : 0 < α) (u : Fin n → Vec d) :
    IsSymMinimizer α u ↔ IsSimplexETF u := by sorry

end NeuralCollapseCE
