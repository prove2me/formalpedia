-- Prove2me | Theorems.Thm_LinearOptimization_integer_polyhedron_points_natGenerated
-- name    : LinearOptimization.integer_polyhedron_points_natGenerated
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-10T03:23:00.297095+00:00
-- url     : https://prove2.me/theorems/ebc8c072-442c-40c3-ab4d-6c850cb75fc0
-- title:
--   Finite integer generators for an integer polyhedron
-- statement:
--   Let $D\in\mathbb{Z}^{m\times n}$ and $d\in\mathbb{Z}^m$, and let $X=\{z\in\mathbb{Z}^n:Dz\ge d\}$. There are finitely many base points $x^1,\ldots,x^k\in\mathbb{R}^n$ and finitely many directions $w^1,\ldots,w^r\in\mathbb{R}^n$ such that
--
--   $$X=\left\{x^i+\sum_{j=1}^r q_jw^j:i\in\{1,\ldots,k\},\ q_j\in\mathbb{Z}_{\ge0}\right\}.$$
--
--   The statement also covers $X=\varnothing$ by allowing $k=0$. It is the finite integer-generator form used in the proof that the integer hull is a polyhedron.
-- source:
--   Bertsimas and Tsitsiklis, Introduction to Linear Optimization (Athena Scientific, 1997), Theorem 11.3, p. 496, proof outlined in Exercise 11.8(a)-(d), p. 525, especially part (c). The all-cases homogenized formulation is obtained via Gordan finite generation of the nonnegative integer solution monoid.

import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Tactic
import Definitions.Def_LinearOptimization_LagrangeanDual

theorem LinearOptimization.integer_polyhedron_points_natGenerated {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) ℤ) (d : Fin m → ℤ) :
    ∃ (k r : ℕ) (x : Fin k → (Fin n → ℝ)) (w : Fin r → (Fin n → ℝ)),
      lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i ↦ (d i : ℝ)) =
        {y | ∃ (i : Fin k) (q : Fin r → ℕ),
          y = x i + ∑ j, (q j : ℝ) • w j} := by sorry
