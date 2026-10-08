-- Prove2me | Theorems.Thm_MatousekLP_SmallestBall_smallest_ball_qp
-- name    : MatousekLP.SmallestBall.smallest_ball_qp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:54:54.872105+00:00
-- url     : https://prove2.me/theorems/cf280b68-f395-42a9-a3d7-f91c292f982b
-- title:
--   Theorem 8.7.4 — the smallest enclosing ball from a convex quadratic program
-- statement:
--   Let $p_1,\dots,p_n$ be points in $\mathbb{R}^d$ with $n\ge 1$, let $P=\{p_1,\dots,p_n\}$, and let $Q$ be the $d\times n$ matrix whose $j$th column is formed by the $d$ coordinates of $p_j$. Consider the optimization problem
--   $$\text{(8.15)}\qquad \text{minimize } x^{T}Q^{T}Qx-\sum_{j=1}^{n}x_j\,p_j^{T}p_j\quad\text{subject to }\ \sum_{j=1}^n x_j=1,\ x\ge 0$$
--   in the variables $x_1,\dots,x_n$. Then the objective function $f(x)=x^TQ^TQx-\sum_{j}x_jp_j^Tp_j$ is convex on $\mathbb{R}^n$, and:
--
--   1. Problem (8.15) has an optimal solution $x^*$.
--   2. There exists a point $p^*$ such that $p^*=Qx^*$ for every optimal solution $x^*$. Moreover, for every optimal solution $x^*$, $-f(x^*)\ge 0$, and the ball with center $p^*$ and squared radius $-f(x^*)$ (radius $\sqrt{-f(x^*)}$) is the unique ball of smallest radius containing $P$.
--
--   In particular the smallest enclosing ball of a finite point set exists and is unique, and it is computed by a convex quadratic program.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin d)` and $x\in\mathbb{R}^n$ is `Fin n → ℝ` (0-based indices). The hypothesis $n\ge 1$ is the book's "points $p_1,\dots,p_n$"; for $n=0$ the feasible set is empty and (i) fails. "Unique ball of smallest radius" is the definition `IsUniqueSmallestEnclosingBall`: the ball contains $P$, no ball containing $P$ is smaller, and any ball containing $P$ of radius at most the optimum has center $p^*$. The equation $p^*=Qx^*$ is stated coordinatewise. Convexity is stated on all of $\mathbb{R}^n$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 190, Theorem 8.7.4 (program (8.15)); P from §8.7, p. 184

import Mathlib
import Definitions.Def_MatousekLP_SmallestBall_Basic

open Matrix

namespace MatousekLP.SmallestBall

/-- Theorem 8.7.4 (Matoušek & Gärtner, p. 190). Let `p₁, …, pₙ ∈ ℝ^d` with `n ≥ 1`, `Q` the
`d × n` matrix with columns `pⱼ`, and `f(x) = xᵀQᵀQx − ∑ⱼ xⱼ pⱼᵀpⱼ`. Then `f` is convex, and
(i) problem (8.15) "minimize `f(x)` subject to `∑ⱼ xⱼ = 1`, `x ≥ 0`" has an optimal solution;
(ii) there is a point `p*` with `p* = Qx*` for every optimal solution `x*`, and for every optimal
`x*` we have `−f(x*) ≥ 0` and the ball with center `p*` and radius `√(−f(x*))` (squared radius
`−f(x*)`) is the unique ball of smallest radius containing `P = {p₁, …, pₙ}`. -/
theorem smallest_ball_qp {d n : ℕ} (hn : 1 ≤ n) (p : Fin n → EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (ballObjective p) ∧
    (∃ x : Fin n → ℝ, IsOptimalBallQP p x) ∧
    ∃ pstar : EuclideanSpace ℝ (Fin d),
      (∀ x : Fin n → ℝ, IsOptimalBallQP p x → ∀ i, pstar i = (pointMatrix p *ᵥ x) i) ∧
      ∀ x : Fin n → ℝ, IsOptimalBallQP p x →
        0 ≤ -ballObjective p x ∧
        IsUniqueSmallestEnclosingBall (Set.range p) pstar (Real.sqrt (-ballObjective p x)) := by sorry

end MatousekLP.SmallestBall
