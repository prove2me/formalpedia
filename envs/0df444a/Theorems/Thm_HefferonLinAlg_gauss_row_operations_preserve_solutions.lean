-- Prove2me | Theorems.Thm_HefferonLinAlg_gauss_row_operations_preserve_solutions
-- name    : HefferonLinAlg.gauss_row_operations_preserve_solutions
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-05T05:10:09.654411+00:00
-- url     : https://prove2.me/theorems/7458dc6f-024e-4df6-82d4-aa7418e6f00d
-- title:
--   Gauss's method preserves the solution set
-- statement:
--   Let $A$ be an $m \times n$ matrix over a field $K$, let $b \in K^m$, and let $M$ be an $m \times m$ matrix whose determinant is a unit, so that $M$ is invertible. Then a vector $x \in K^n$ satisfies $Ax = b$ if and only if it satisfies $(MA)x = Mb$. Each of Gauss's three elementary row operations — swapping two rows, scaling a row by a nonzero constant, and adding a multiple of one row to another — is left multiplication by such an invertible $M$, so this is the statement that row reduction carries a linear system to an equivalent one.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter One, Section I.1, Theorem 1.5, p. 12

import Mathlib

open Matrix

namespace HefferonLinAlg

theorem gauss_row_operations_preserve_solutions
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (M : Matrix (Fin m) (Fin m) K) (hM : IsUnit M.det) (x : Fin n → K) :
    A *ᵥ x = b ↔ (M * A) *ᵥ x = M *ᵥ b := by
  sorry

end HefferonLinAlg
