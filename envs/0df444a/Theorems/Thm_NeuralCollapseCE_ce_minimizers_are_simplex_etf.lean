-- Prove2me | Theorems.Thm_NeuralCollapseCE_ce_minimizers_are_simplex_etf
-- name    : NeuralCollapseCE.ce_minimizers_are_simplex_etf
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:11:47.059478+00:00
-- url     : https://prove2.me/theorems/39b46756-56ce-4339-8df5-df23c2dcf5db
-- title:
--   Theorem 1: neural collapse for the cross-entropy loss
-- statement:
--   Let $n\ge2$ and $d\ge n-1$. Consider the problem of minimising the cross-entropy loss
--
--   $$\mathcal{L}(u,v)=\sum_{i=1}^n\log\frac{\sum_{j=1}^n e^{\langle v_j,u_i\rangle}}{e^{\langle v_i,u_i\rangle}}$$
--
--   over $u_i,v_i\in\mathbb{R}^d$ with $\|u_i\|=\|v_i\|=1$, $i=1,\dots,n$. A pair $(u,v)$ is a global minimiser if and only if $\{u_i\}_{i=1}^n$ is a simplex equiangular tight frame and $v_i=u_i$ for all $i$.
--
--   This is the neural collapse phenomenon for unconstrained features with cross-entropy loss: at the optimum the class features form a simplex ETF and coincide with the classifier vectors.
--
--   **Formalization Note** "The global minimum corresponds to" is stated as an equivalence. The hypothesis $n\ge2$ is implicit in the paper and necessary: for $n=1$ the loss is identically $0$, so every pair of unit vectors, including $v_1\ne u_1$, is a minimiser.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 1.2, Theorem 1, eq. (2), p. 2; proof in Section 3, pp. 6-8

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory Filter Topology Asymptotics

namespace NeuralCollapseCE

theorem ce_minimizers_are_simplex_etf {n d : ℕ} (hn : 2 ≤ n) (hd : n ≤ d + 1)
    (u v : Fin n → Vec d) :
    IsCEMinimizer u v ↔ (IsSimplexETF u ∧ v = u) := by sorry

end NeuralCollapseCE
