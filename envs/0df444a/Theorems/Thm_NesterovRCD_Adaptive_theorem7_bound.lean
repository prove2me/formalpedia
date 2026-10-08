-- Prove2me | Theorems.Thm_NesterovRCD_Adaptive_theorem7_bound
-- name    : NesterovRCD.Adaptive.theorem7_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:14.356831+00:00
-- url     : https://prove2.me/theorems/9af7da75-5e00-4f1b-8926-c46f2ee32397
-- title:
--   Theorem 7, item 1 — $0<\hat L_i\le L_i$ at the beginning of each iteration of RACDM
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable with coordinate-wise Lipschitz partial derivatives (2.2) with constants $L_1,\dots,L_n$, and let the initial estimates satisfy $L_i^0\in(0,L_i]$ for every $i$. Run RACDM$(x_0)$ (6.1) from any $x_0$ along any sequence of drawn coordinates $i_0,\dots,i_{k-1}$. Then at the beginning of iteration $k$ every estimate satisfies
--   $$0<\hat L_i\le L_i,\qquad i=1,\dots,n .$$
--
--   This is item 1 of Theorem 7. It says that the halving in step 3 restores the invariant "$\hat L_i$ is a lower bound of $L_i$", so the doubling loop is always entered under the hypothesis of (6.4); it also supplies the bound $\hat L_i\le L_i$ used to count the derivative evaluations in item 3.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (scalar coordinates: the paper sets $N=n$ in §6.1), coordinates are indexed $0,\dots,n-1$ for the paper's $1,\dots,n$, and the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$, as in the published definition `ConvexOptAlg_CoordDescent_Defs` that this mission reuses (its `IsCoordSmooth f g L` is (2.2) with one-dimensional blocks and $|\cdot|$ as block norm; it includes differentiability). The statement holds for every sequence of draws, hence at every iteration of every realization. Positivity of $\hat L_i$ is implicit in the paper (the method divides by $\hat L_i$) and is part of the conclusion. Step 3 is read as $\hat L_{i_k}:=\frac12\hat L_{i_k}$ (the printed $L_{i_k}:=\frac12L_{i_k}$ is a typo; see the definition). The standing convexity of $f$ and the existence of a minimizer are not used and not assumed.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 18, Theorem 7, item 1

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs
import Definitions.Def_NesterovRCD_Adaptive_RACDM

namespace NesterovRCD.Adaptive

open ConvexOptAlg.CoordDescent

/-- Theorem 7, item 1, p. 18: at the beginning of each iteration of RACDM (6.1), every estimate
satisfies `0 < L̂_i ≤ L_i`. -/
theorem theorem7_bound {n : ℕ} (f : Vec n → ℝ) (g : Vec n → Vec n) (L : Fin n → ℝ)
    (hL : IsCoordSmooth f g L) (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i)
    (x0 : Vec n) (k : ℕ) (idx : Fin k → Fin n) (i : Fin n) :
    0 < (racdm g L0 x0 k idx).2 i ∧ (racdm g L0 x0 k idx).2 i ≤ L i := by sorry

end NesterovRCD.Adaptive
