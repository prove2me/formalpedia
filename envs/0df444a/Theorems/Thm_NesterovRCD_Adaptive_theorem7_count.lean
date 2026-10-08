-- Prove2me | Theorems.Thm_NesterovRCD_Adaptive_theorem7_count
-- name    : NesterovRCD.Adaptive.theorem7_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:36.194524+00:00
-- url     : https://prove2.me/theorems/043d5532-ca54-46c4-947c-08a1da936e3e
-- title:
--   Theorem 7, item 3, (6.3) — $N_k\le 2(k+1)+\sum_i\log_2(L_i/L_i^0)$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable with coordinate-wise Lipschitz partial derivatives (2.2) with constants $L_1,\dots,L_n$, and let the initial estimates satisfy $L_i^0\in(0,L_i]$. Run RACDM$(x_0)$ (6.1) from any $x_0$ along any sequence of drawn coordinates $i_0,\dots,i_k$, and let $N_k$ be the total number of computations of directional derivatives in iterations $0,\dots,k$: iteration $j$, which performs $d_j$ doublings in its loop, computes $\nabla_{i_j}f$ at $d_j+1$ trial points. Then
--   $$N_k\ \le\ 2(k+1)+\sum_{i=1}^n\log_2\frac{L_i}{L_i^0}.$$
--
--   This is item 3 of Theorem 7: on average the adaptive method costs about two directional derivatives per iteration, plus a one-time overhead logarithmic in the ratio of the true constants to the initial guesses.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (scalar coordinates: the paper sets $N=n$ in §6.1), coordinates are indexed $0,\dots,n-1$ for the paper's $1,\dots,n$, and the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$, as in the published definition `ConvexOptAlg_CoordDescent_Defs` that this mission reuses (its `IsCoordSmooth f g L` is (2.2) with one-dimensional blocks and $|\cdot|$ as block norm; it includes differentiability). The count per iteration, $p_{i_j}(j)=d_j+1$, is the one fixed by the paper's proof ("$\hat L'_i=\frac12\cdot2^{p_i(j)-1}\cdot\hat L_i$, in other words $p_i(j)=2+\log_2[\hat L'_i/\hat L_i]$"): it counts the evaluations of $\nabla_{i_j}f$ at the trial points and not the evaluation of $\nabla_{i_j}f(x_j)$; counting that one too would give $3(k+1)+\sum_i\log_2(L_i/L_i^0)$. The statement holds for every sequence of draws. The standing convexity of $f$ and the existence of a minimizer are not used and not assumed. $\log_2$ is `Real.logb 2`, applied to $L_i/L_i^0\ge1$.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 18, Theorem 7, item 3, (6.3); p_i(j) and M_i in its proof, p. 19

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs
import Definitions.Def_NesterovRCD_Adaptive_RACDM

namespace NesterovRCD.Adaptive

open ConvexOptAlg.CoordDescent

/-- Theorem 7, item 3, (6.3), p. 18: after iteration `k` (iterations `0, …, k`, draws `idx`),
the total number `N_k` of computations of directional derivatives in RACDM (6.1) satisfies
`N_k ≤ 2(k + 1) + Σ_i log₂(L_i / L⁰_i)`. -/
theorem theorem7_count {n : ℕ} (f : Vec n → ℝ) (g : Vec n → Vec n) (L : Fin n → ℝ)
    (hL : IsCoordSmooth f g L) (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i)
    (x0 : Vec n) (k : ℕ) (idx : Fin (k + 1) → Fin n) :
    (numDerivs g L0 x0 k idx : ℝ) ≤ 2 * (k + 1) + ∑ i, Real.logb 2 (L i / L0 i) := by sorry

end NesterovRCD.Adaptive
