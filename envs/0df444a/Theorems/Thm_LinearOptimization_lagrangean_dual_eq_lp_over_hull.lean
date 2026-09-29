-- Prove2me | Theorems.Thm_LinearOptimization_lagrangean_dual_eq_lp_over_hull
-- name    : LinearOptimization.lagrangean_dual_eq_lp_over_hull
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T16:00:35.672191+00:00
-- url     : https://prove2.me/theorems/ce761c67-92b7-4237-b174-f7d6162c40b3
-- title:
--   Lagrangean dual equals the LP over the convex hull of $X$
-- statement:
--   **(Theorem 11.4, GOAL — Bertsimas & Tsitsiklis, p. 496, the central result of Section 11.4.)** In the setting of Section 11.4 (integer program (11.5): minimize $c'x$ subject to $Ax \ge b$, $Dx \ge d$, $x$ integer, with $A$, $D$, $b$, $c$, $d$ of integer entries; $X = \{x\ \text{integer} \mid Dx \ge d\}$; $Z(p) = \min_{x \in X}(c'x + p'(b - Ax))$ for $p \ge 0$; $Z_D = \max_{p \ge 0} Z(p)$):
--
--   the optimal value $Z_D$ of the Lagrangean dual is equal to the optimal cost of the following linear programming problem (11.9):
--
--   $$\begin{aligned}\text{minimize}\quad & c'x\\ \text{subject to}\quad & Ax \ge b\\ & x \in CH(X),\end{aligned}$$
--
--   where $CH(X)$ is the convex hull of the set $X$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 11.4, p. 496

import Mathlib.Analysis.Convex.Hull
import Definitions.Def_LinearOptimization_IntegerProgram
import Definitions.Def_LinearOptimization_LagrangeanDual


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 11.4 (p. 496).** The Lagrangean dual equals the linear
program over the convex hull of `X`:
`Z_D = min {c'x | Ax ≥ b, x ∈ CH(X)}` (as `EReal` values), provided
`X = ∅` or the right-hand LP is feasible. -/

theorem LinearOptimization.lagrangean_dual_eq_lp_over_hull {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℤ) (b : Fin m₁ → ℤ) (c : Fin n → ℤ)
    (D : Matrix (Fin m₂) (Fin n) ℤ) (d : Fin m₂ → ℤ)
    (hguard :
      lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ)) = ∅ ∨
      {x : Fin n → ℝ | (fun i => (b i : ℝ)) ≤ (A.map ((↑) : ℤ → ℝ)).mulVec x ∧
        x ∈ convexHull ℝ (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ))
          (fun i => (d i : ℝ)))}.Nonempty) :
    lagrangeanDualValue (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))
        (fun j => (c j : ℝ))
        (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))) =
      lpValue (fun j => (c j : ℝ))
        {x : Fin n → ℝ |
          (fun i => (b i : ℝ)) ≤ (A.map ((↑) : ℤ → ℝ)).mulVec x ∧
          x ∈ convexHull ℝ (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ))
            (fun i => (d i : ℝ)))} := by
  sorry
