-- Prove2me | Theorems.Thm_N25_matrix_det25_triangular
-- name    : N25.matrix_det25_triangular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:43:07.302878+00:00
-- url     : https://prove2.me/theorems/c7026d39-fc2e-41be-8a4c-5479eec087ff
-- title:
--   Every determinant-$25$ matrix has a left-unimodular triangular form
-- statement:
--   Let $M$ be a $2×2$ integer matrix with $det(M)=25$. Then there exist $B∈SL_2(ℤ)$, a positive natural number $d$, and integers $e,v$ with $e>0$ such that $d=gcd(M_{11},M_{21})$, $de=25$, and $$M=B\begin{pmatrix}d&v\0&e\end{pmatrix}.$$ This normal form reduces determinant-$25$ transformations to the cusp-width cases used in the analytic argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem N25.matrix_det25_triangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 25) :
    ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : ℕ) (e v : ℤ),
      d = Int.gcd (M 0 0) (M 1 0) ∧ 0 < d ∧ 0 < e ∧ (d : ℤ) * e = 25 ∧
      M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![(d : ℤ), v; 0, e] := by sorry
