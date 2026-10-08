-- Prove2me | Theorems.Thm_MatousekLP_InteriorPoint_barrier_superlevel_bounded
-- name    : MatousekLP.InteriorPoint.barrier_superlevel_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:44:17.510973+00:00
-- url     : https://prove2.me/theorems/f64ba2af-bccd-40e3-8424-521e9c76ea2c
-- title:
--   Claim in the proof of Lemma 7.2.1 — superlevel sets of the barrier are bounded
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$. Suppose the linear program (7.2) (maximize $c^{T}x$ subject to $Ax=b$, $x\ge 0$) has a feasible solution $\tilde x>0$, and its dual (7.5) (minimize $b^{T}y$ subject to $A^{T}y\ge c$) has a feasible solution $\tilde y$ whose slack vector $\tilde s=A^{T}\tilde y-c$ satisfies $\tilde s>0$. Fix $\mu>0$ and let $f_\mu(x)=c^{T}x+\mu\sum_{j=1}^n\ln x_j$. Then the set
--
--   $$Q=\{x\in\mathbb{R}^n:\ Ax=b,\ x>0,\ f_\mu(x)\ge f_\mu(\tilde x)\}$$
--
--   is bounded.
--
--   This is the compactness step behind the existence of a maximizer of the barrier problem, and hence of the point $x^*(\mu)$ of the central path.
--
--   **Formalization Note** $x>0$ means every coordinate is strictly positive; indices are `Fin n`. Boundedness is `Bornology.IsBounded` in the sup-norm topology of `Fin n → ℝ`, which is equivalent to boundedness in any norm.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §7.2, p. 121, Claim in the proof of Lemma 7.2.1

import Mathlib
import Definitions.Def_MatousekLP_InteriorPoint_CentralPath

namespace MatousekLP.InteriorPoint

open Matrix

/-- Claim in the proof of Lemma 7.2.1 (Matoušek & Gärtner, p. 121). Let `A` be an `m × n`
matrix of rank `m`, let `x̃ > 0` satisfy `Ax̃ = b`, let `ỹ` satisfy `Aᵀỹ − c > 0`, and let
`μ > 0`. Then the set `Q = {x ∈ ℝⁿ : Ax = b, x > 0, f_μ(x) ≥ f_μ(x̃)}` is bounded. -/
theorem barrier_superlevel_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (xt : Fin n → ℝ) (hxt : IsPrimalInterior A b xt)
    (yt : Fin m → ℝ) (hyt : IsDualInterior A c yt) (μ : ℝ) (hμ : 0 < μ) :
    Bornology.IsBounded
      {x : Fin n → ℝ | IsPrimalInterior A b x ∧ barrier c μ xt ≤ barrier c μ x} := by sorry

end MatousekLP.InteriorPoint
