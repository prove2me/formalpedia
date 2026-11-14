-- Prove2me | Theorems.Thm_LatticePrepro_exists_det_submatrix_ne_zero
-- name    : LatticePrepro.exists_det_submatrix_ne_zero
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:24:51.852041+00:00
-- url     : https://prove2.me/theorems/85e42a26-40cd-4539-8f8e-963ac54d59b1
-- title:
--   A matrix of rank $k$ has a nonzero $k \times k$ minor
-- statement:
--   Let $K$ be a field, let $m$ and $n$ be finite index sets, and let $A = (A_{ij}) \in K^{m \times n}$ be a matrix of rank $k$. Then $A$ has a nonsingular $k \times k$ submatrix: there are row indices $r_1, \dots, r_k \in m$ and column indices $c_1, \dots, c_k \in n$ such that
--   $$\det\bigl(A_{r_i, c_j}\bigr)_{1 \le i, j \le k} \neq 0.$$
--
--   This is one direction of the characterization of the rank as the size of a largest nonvanishing minor. It is used in Lemma A.6, the rank bound for the polynomial matrix $\mathbf H(X)$ of an evaluation table: a nonsingular minor of the evaluation $\mathbf H(\gamma)$ at the generator $\gamma$ of the moment field selects a square submatrix of $\mathbf H(X)$ whose determinant is a nonzero polynomial.
--
--   **Formalization Note**: The row and column choices are maps $r\colon \mathrm{Fin}\,k \to m$ and $c\colon \mathrm{Fin}\,k \to n$ (not required to be injective in the statement), the submatrix is `A.submatrix r c`, and the rank is Mathlib's `Matrix.rank`. For $k = 0$ the statement is trivial, since the empty determinant is $1$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in the proof of Lemma A.6 (\label{lem:table-rank}); Lean: LatticePrepro/Basic/Matrix.lean, LatticePrepro.exists_det_submatrix_ne_zero

import Mathlib

open Polynomial Matrix
variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

theorem LatticePrepro.exists_det_submatrix_ne_zero [Fintype m] (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ (r : Fin k → m) (c : Fin k → n), (A.submatrix r c).det ≠ 0 := by sorry
