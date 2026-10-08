-- Prove2me | Theorems.Thm_NesterovRCD_Adaptive_step_decrease
-- name    : NesterovRCD.Adaptive.step_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:28.484176+00:00
-- url     : https://prove2.me/theorems/0d639530-85ca-4754-b493-0e393b393dcd
-- title:
--   Proof of Theorem 7 — one RACDM iteration decreases $f$ by at least $3(\nabla_if(x))^2/(8L_i)$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and differentiable with coordinate-wise Lipschitz partial derivatives (2.2) with constants $L_1,\dots,L_n$. Let $x\in\mathbb R^n$, let $\hat L$ be a vector of estimates, and let $i$ be a coordinate with $0<\hat L_i\le L_i$. If $x^+$ is the point produced by one iteration of RACDM (6.1) on coordinate $i$ from the state $(x,\hat L)$ (doubling loop, then the step with the accepted estimate), then
--   $$f(x)-f(x^+)\ \ge\ \frac{3}{8L_i}\,\big(\nabla_i f(x)\big)^2 .$$
--
--   This is the one-step decrease in the proof of Theorem 7 (p. 19). It replaces the bound $f(x)-f(T_i(x))\ge(\nabla_if(x))^2/(2L_i)$ of (2.4) for the step with the known constant $L_i$; the factor $3/8$ instead of $1/2$ is the price of not knowing $L_i$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (scalar coordinates: the paper sets $N=n$ in §6.1), coordinates are indexed $0,\dots,n-1$ for the paper's $1,\dots,n$, and the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$, as in the published definition `ConvexOptAlg_CoordDescent_Defs` that this mission reuses (its `IsCoordSmooth f g L` is (2.2) with one-dimensional blocks and $|\cdot|$ as block norm; it includes differentiability). The paper derives the bound from inequality (2.1.17) of Nesterov's *Introductory Lectures*, which needs the convexity of $f$ along the coordinate line; convexity of $f$ is the paper's standing assumption (2.1) and is a hypothesis here. In the paper the entry condition $\hat L_{i_k}\le L_{i_k}$ comes from item 1; here it is a hypothesis on an arbitrary state, together with $\hat L_i>0$ (implicit in the paper).
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 19, proof of Theorem 7 (first display)

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs
import Definitions.Def_NesterovRCD_Adaptive_RACDM

namespace NesterovRCD.Adaptive

open ConvexOptAlg.CoordDescent

/-- Proof of Theorem 7, p. 19: for convex `f`, one iteration of RACDM (6.1) on coordinate `i`
from `(x, L̂)` with `0 < L̂_i ≤ L_i` decreases `f` by at least `3 (∇_i f(x))² / (8 L_i)`. -/
theorem step_decrease {n : ℕ} (f : Vec n → ℝ) (g : Vec n → Vec n)
    (hconv : ConvexOn ℝ Set.univ f) (L : Fin n → ℝ) (hL : IsCoordSmooth f g L)
    (x : Vec n) (Lh : Fin n → ℝ) (i : Fin n) (hpos : 0 < Lh i) (hle : Lh i ≤ L i) :
    3 / (8 * L i) * g x i ^ 2 ≤ f x - f (racdmStep g (x, Lh) i).1 := by sorry

end NesterovRCD.Adaptive
