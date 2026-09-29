-- Prove2me | Theorems.Thm_LinearOptimization_fourier_motzkin_eliminate_is_polyhedron
-- name    : LinearOptimization.fourier_motzkin_eliminate_is_polyhedron
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T16:24:16.563288+00:00
-- url     : https://prove2.me/theorems/6df0cbfd-26b3-4e0b-9e6e-bc8b4cc5ee5b
-- title:
--   One Fourier–Motzkin elimination step produces a polyhedron
-- statement:
--   For a system of linear inequalities in $n+1$ variables, perform one Fourier–Motzkin elimination step on the last variable. The retained zero-coefficient rows and every compatible positive/negative row pair form a finite system of inequalities in the first $n$ variables. Consequently, there exist a natural number $m'$, a matrix $A'\in\mathbb{R}^{m'\times n}$, and a vector $b'\in\mathbb{R}^{m'}$ such that
--
--   $$
--   \operatorname{FM}(A,b)=\{y\in\mathbb{R}^n\mid A'y\ge b'\}.
--   $$
--
--   This theorem records the finite polyhedral presentation produced by one elimination step and is the reusable bridge from Theorem 2.10 to Corollary 2.4.
--
--   **Formalization Note** The row type of the new system is the finite disjoint union of zero-coefficient rows and pairs consisting of a positive-coefficient row and a negative-coefficient row.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §2.8 Elimination algorithm pp. 71–72 and Theorem 2.10 p. 73; finite-presentation consequence used in Corollary 2.4 p. 74

import Definitions.Def_FourierMotzkinStep

theorem LinearOptimization.fourier_motzkin_eliminate_is_polyhedron {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (b : Fin m → ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      fourierMotzkinEliminate A b = polyhedron A' b' := by
  sorry
