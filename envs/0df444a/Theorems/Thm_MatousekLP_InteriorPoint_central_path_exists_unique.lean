-- Prove2me | Theorems.Thm_MatousekLP_InteriorPoint_central_path_exists_unique
-- name    : MatousekLP.InteriorPoint.central_path_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:44:34.306373+00:00
-- url     : https://prove2.me/theorems/f8619610-5cb4-4a1c-9770-4f3f96ec7a0d
-- title:
--   Lemma 7.2.1 — existence and uniqueness of the primal–dual central path
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$, and consider the linear program (7.2), maximize $c^{T}x$ subject to $Ax=b$, $x\ge 0$, and its dual (7.5), minimize $b^{T}y$ subject to $A^{T}y\ge c$. Suppose (7.2) has a feasible solution $\tilde x>0$ and (7.5) has a feasible solution $\tilde y$ whose slack vector $\tilde s=A^{T}\tilde y-c$ satisfies $\tilde s>0$; that is, both programs have an interior feasible point.
--
--   Then for every $\mu>0$ the system
--
--   $$Ax=b,\qquad A^{T}y-s=c,\qquad (s_1x_1,\dots,s_nx_n)=\mu\mathbf 1,\qquad x,s\ge 0 \tag{7.4}$$
--
--   in the unknowns $x,s\in\mathbb{R}^n$, $y\in\mathbb{R}^m$ has exactly one solution $x^*(\mu),y^*(\mu),s^*(\mu)$, and $x^*(\mu)$ is the unique maximizer of the barrier function $f_\mu(x)=c^{T}x+\mu\sum_{j=1}^n\ln x_j$ subject to $Ax=b$ and $x>0$.
--
--   The set $\{(x^*(\mu),y^*(\mu),s^*(\mu)):\mu>0\}$ is the primal–dual central path of (7.2), the curve that path-following interior point methods track.
--
--   **Formalization Note** Indices are `Fin n` and `Fin m`. Uniqueness of the triple is stated as: one solution exists, and every solution of (7.4) equals it. "Unique maximizer" means $Ax^*=b$, $x^*>0$, and $f_\mu(x)<f_\mu(x^*)$ for every other $x$ with $Ax=b$, $x>0$; the barrier is never evaluated at a point with a nonpositive coordinate in this comparison. The rank hypothesis is the standing assumption of (7.2).
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §7.2, p. 121, Lemma 7.2.1 (with (7.2) p. 119, (7.4) and (7.5) p. 120)

import Mathlib
import Definitions.Def_MatousekLP_InteriorPoint_CentralPath

namespace MatousekLP.InteriorPoint

open Matrix

/-- Lemma 7.2.1 (Matoušek & Gärtner, p. 121). Let `A` be an `m × n` matrix of rank `m`.
Suppose the linear program (7.2) `maximize cᵀx subject to Ax = b, x ≥ 0` has a feasible
solution `x̃ > 0` and the dual (7.5) `minimize bᵀy subject to Aᵀy ≥ c` has a feasible solution
`ỹ` whose slack vector `s̃ = Aᵀỹ − c` satisfies `s̃ > 0`. Then for every `μ > 0` the system
(7.4) has a unique solution `x*(μ), y*(μ), s*(μ)`, and `x*(μ)` is the unique maximizer of
`f_μ` subject to `Ax = b` and `x > 0`. -/
theorem central_path_exists_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (xt : Fin n → ℝ) (hxt : IsPrimalInterior A b xt)
    (yt : Fin m → ℝ) (hyt : IsDualInterior A c yt) :
    ∀ μ : ℝ, 0 < μ →
      ∃ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ),
        CentralPathSystem A b c μ x y s ∧
        (∀ (x' : Fin n → ℝ) (y' : Fin m → ℝ) (s' : Fin n → ℝ),
          CentralPathSystem A b c μ x' y' s' → x' = x ∧ y' = y ∧ s' = s) ∧
        IsUniqueBarrierMaximizer A b c μ x := by sorry

end MatousekLP.InteriorPoint
