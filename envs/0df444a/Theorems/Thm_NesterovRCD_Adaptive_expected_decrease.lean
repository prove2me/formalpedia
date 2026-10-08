-- Prove2me | Theorems.Thm_NesterovRCD_Adaptive_expected_decrease
-- name    : NesterovRCD.Adaptive.expected_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:19.605887+00:00
-- url     : https://prove2.me/theorems/f4cca0a9-2900-4540-a057-4573170e1857
-- title:
--   Proof of Theorem 7 — $f(x_k)-\mathbb E_{i_k}f(x_{k+1})\ge\frac{3}{8n}(\|\nabla f(x_k)\|_1^*)^2$
-- statement:
--   Let $n\ge1$ and let $f:\mathbb R^n\to\mathbb R$ be convex and differentiable with coordinate-wise Lipschitz partial derivatives (2.2) with constants $L_1,\dots,L_n$. Write
--   $$\|g\|_1^*=\Big(\sum_{i=1}^n\frac{g_i^2}{L_i}\Big)^{1/2}$$
--   for the dual norm of (2.7) with $\alpha=1$. Let $x\in\mathbb R^n$ and let the estimates satisfy $0<\hat L_i\le L_i$ for every $i$. Draw the coordinate $i$ uniformly from $\{1,\dots,n\}$ (the counter $\mathcal R_0$) and let $x^+_i$ be the point produced by one iteration of RACDM (6.1) on coordinate $i$ from the state $(x,\hat L)$. Then
--   $$f(x)-\sum_{i=1}^n\frac1n\,f(x^+_i)\ \ge\ \frac{3}{8n}\,\big(\|\nabla f(x)\|_1^*\big)^2 .$$
--
--   This is the expected decrease of one RACDM iteration (p. 19), the analogue of (2.13) for the adaptive method; it is the inequality from which the rate (6.2) follows by the argument of Theorem 1.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (scalar coordinates: the paper sets $N=n$ in §6.1), coordinates are indexed $0,\dots,n-1$ for the paper's $1,\dots,n$, and the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$, as in the published definition `ConvexOptAlg_CoordDescent_Defs` that this mission reuses (its `IsCoordSmooth f g L` is (2.2) with one-dimensional blocks and $|\cdot|$ as block norm; it includes differentiability). The uniform probabilities are the published `pGamma L 0 i` $=L_i^0/\sum_jL_j^0=1/n$. The norm is the published `wnormDual L 1`. The hypotheses $0<\hat L_i\le L_i$ for all $i$ are what item 1 of Theorem 7 provides at the beginning of each iteration; $n\ge1$ is implicit in the paper (for $n=0$ there are no coordinates to draw).
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 19, proof of Theorem 7 (second display)

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs
import Definitions.Def_NesterovRCD_Adaptive_RACDM

namespace NesterovRCD.Adaptive

open ConvexOptAlg.CoordDescent

/-- Proof of Theorem 7, p. 19: for convex `f` and estimates `0 < L̂_i ≤ L_i`, one iteration of
RACDM (6.1) with the coordinate drawn uniformly (the counter `R_0`, `p_0(i) = 1/n`) satisfies
`f(x) − E_i f(x⁺) ≥ 3 (‖∇f(x)‖*_1)² / (8n)`. -/
theorem expected_decrease {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ) (g : Vec n → Vec n)
    (hconv : ConvexOn ℝ Set.univ f) (L : Fin n → ℝ) (hL : IsCoordSmooth f g L)
    (x : Vec n) (Lh : Fin n → ℝ) (hLh : ∀ i, 0 < Lh i ∧ Lh i ≤ L i) :
    3 / (8 * n) * wnormDual L 1 (g x) ^ 2 ≤
      f x - ∑ i, pGamma L 0 i * f (racdmStep g (x, Lh) i).1 := by sorry

end NesterovRCD.Adaptive
