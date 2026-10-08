-- Prove2me | Theorems.Thm_NesterovRCD_Adaptive_theorem7_rate
-- name    : NesterovRCD.Adaptive.theorem7_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:47.677653+00:00
-- url     : https://prove2.me/theorems/5d3a55e1-811e-4dd0-a260-25e1ef648328
-- title:
--   Theorem 7, item 2, (6.2) — RACDM satisfies $\varphi_k-f^*\le 8nR_1^2(x_0)/(16+3k)$
-- statement:
--   Let $n\ge1$ and let $f:\mathbb R^n\to\mathbb R$ be convex and differentiable with coordinate-wise Lipschitz partial derivatives (2.2) with constants $L_1,\dots,L_n$:
--   $$|\nabla_i f(x+ue_i)-\nabla_i f(x)|\le L_i|u|\qquad(x\in\mathbb R^n,\ u\in\mathbb R,\ i=1,\dots,n).$$
--   Assume $f$ attains its minimum $f^*=f(x^*)$. Let $\|x\|_1=\big(\sum_iL_ix_i^2\big)^{1/2}$ be the norm (2.7) with $\alpha=1$, and let $R\ge R_1(x_0)$, that is, $\|x-y^*\|_1\le R$ for every $x$ with $f(x)\le f(x_0)$ and every minimizer $y^*$ of $f$. Run RACDM$(x_0)$ (6.1) with initial estimates $L_i^0\in(0,L_i]$ and coordinates $i_0,i_1,\dots$ drawn independently and uniformly from $\{1,\dots,n\}$, and let $\varphi_k=\mathbb E f(x_k)$ be the expectation over the first $k$ draws. Then for every $k\ge0$,
--   $$\varphi_k-f^*\ \le\ \frac{8nR^2}{16+3k}.$$
--
--   This is item 2 of Theorem 7, the main result of §6.1: a coordinate descent method that only has lower bounds $L_i^0$ on the coordinate Lipschitz constants, and adjusts them by doubling and halving without computing function values, keeps the $O(nR_1^2(x_0)/k)$ rate of RCDM$(0,x_0)$ (compare (2.14), $\varphi_k-f^*\le 2nR_1^2(x_0)/(k+4)$) at the cost of a constant factor.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (scalar coordinates: the paper sets $N=n$ in §6.1), coordinates are indexed $0,\dots,n-1$ for the paper's $1,\dots,n$, and the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$, as in the published definition `ConvexOptAlg_CoordDescent_Defs` that this mission reuses (its `IsCoordSmooth f g L` is (2.2) with one-dimensional blocks and $|\cdot|$ as block norm; it includes differentiability). The expectation is the published `rcdExpect L 0 k`, a finite sum over all draws $(i_0,\dots,i_{k-1})$ weighted by $\prod_s p_0(i_s)$, $p_0\equiv1/n$; no measure theory is involved. The paper's $R_1(x_0)=\max_x\{\max_{x^*\in X^*}\|x-x^*\|_1: f(x)\le f(x_0)\}$ is not computed: the theorem takes any upper bound $R$ of it (when the maximum is finite it is the least such $R$, so the statement is the paper's). The paper's standing assumption "$X^*$ nonempty" is the hypothesis that $x^*$ minimizes $f$; "$X^*$ bounded" is implied by the existence of $R$. The initial estimates are positive and at most $L_i$ as in the setup of (6.1); $n\ge1$ is implicit in the paper. Step 3 of (6.1) is read as $\hat L_{i_k}:=\frac12\hat L_{i_k}$ (a typo in the paper; see the definition).
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 18, Theorem 7, item 2, (6.2); R_1(x_0) as defined in Theorem 1, p. 7

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs
import Definitions.Def_NesterovRCD_Adaptive_RACDM

namespace NesterovRCD.Adaptive

open ConvexOptAlg.CoordDescent

/-- Theorem 7, item 2, (6.2), p. 18: for convex, coordinate-wise smooth `f` with a minimizer
`x*`, initial estimates `L⁰_i ∈ (0, L_i]`, and `R ≥ R_1(x₀)` (every point of the level set
`{f ≤ f(x₀)}` is within `‖·‖_1`-distance `R` of every minimizer), RACDM(x₀) with uniform draws
satisfies `φ_k − f* ≤ 8 n R² / (16 + 3k)` for every `k ≥ 0`, where `φ_k = E f(x_k)`. -/
theorem theorem7_rate {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ) (g : Vec n → Vec n)
    (hconv : ConvexOn ℝ Set.univ f) (L : Fin n → ℝ) (hL : IsCoordSmooth f g L)
    (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i) (x0 xs : Vec n)
    (hxs : ∀ y, f xs ≤ f y) (R : ℝ)
    (hR : ∀ x, f x ≤ f x0 → ∀ ys, (∀ y, f ys ≤ f y) → wnorm L 1 (x - ys) ≤ R) (k : ℕ) :
    rcdExpect L 0 k (fun idx => f (racdm g L0 x0 k idx).1) - f xs ≤
      8 * n * R ^ 2 / (16 + 3 * k) := by sorry

end NesterovRCD.Adaptive
