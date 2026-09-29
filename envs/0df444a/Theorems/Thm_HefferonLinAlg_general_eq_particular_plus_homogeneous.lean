-- Prove2me | Theorems.Thm_HefferonLinAlg_general_eq_particular_plus_homogeneous
-- name    : HefferonLinAlg.general_eq_particular_plus_homogeneous
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-05T05:10:22.571891+00:00
-- url     : https://prove2.me/theorems/ddc7a835-124c-47ac-ac71-ae9f03aff5d2
-- title:
--   General = particular + homogeneous
-- statement:
--   Let $A$ be an $m \times n$ matrix over a field $K$, let $b \in K^m$, and suppose $p \in K^n$ is one particular solution, $Ap = b$. Then the solution set of $Ax = b$ is exactly $\{\, p + h : Ah = 0 \,\}$. Every solution is the particular solution plus a solution of the associated homogeneous system, and conversely every such sum solves the system. This is the structural description of a solution set that Hefferon returns to throughout the book.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter One, Section I.3, Theorem 3.1, p. 33

import Mathlib

open Matrix

namespace HefferonLinAlg

theorem general_eq_particular_plus_homogeneous
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (p : Fin n → K) (hp : A *ᵥ p = b) :
    {x : Fin n → K | A *ᵥ x = b} = {x : Fin n → K | ∃ h, A *ᵥ h = 0 ∧ x = p + h} := by
  sorry

end HefferonLinAlg
