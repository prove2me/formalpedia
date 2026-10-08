-- Prove2me | Theorems.Thm_MatousekLP_Integrality_append_unit_column_totallyUnimodular
-- name    : MatousekLP.Integrality.append_unit_column_totallyUnimodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:17:17.807176+00:00
-- url     : https://prove2.me/theorems/f2ac7bdd-3bba-439d-9381-c8af79c4ebeb
-- title:
--   Lemma 8.2.3 — appending a unit column preserves total unimodularity
-- statement:
--   A real matrix is **totally unimodular** if every square submatrix (obtained by deleting some rows and some columns) has determinant $0$, $1$ or $-1$.
--
--   Let $A$ be a totally unimodular $m \times n$ matrix and let $e_i \in \mathbb{R}^m$ be the $i$-th unit vector. Then the $m \times (n+1)$ matrix
--   $$
--   \bar A = \bigl(A \mid e_i\bigr),
--   $$
--   obtained from $A$ by appending $e_i$ as a new last column, is totally unimodular as well.
--
--   Applied repeatedly, the lemma shows that $(A \mid I_m)$ is totally unimodular whenever $A$ is; this is how slack variables are added in the proof of Lemma 8.2.4.
--
--   **Formalization Note** Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular`, which is the book's definition. The new column is placed at index $n$ of `Fin (n+1)` with `Fin.snoc`; indices are 0-based.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 145, Lemma 8.2.3 (definition of totally unimodular: p. 144)

import Mathlib

namespace MatousekLP.Integrality

theorem append_unit_column_totallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.IsTotallyUnimodular) (i : Fin m) :
    (Matrix.of fun r : Fin m =>
      (Fin.snoc (α := fun _ => ℝ) (A r) (if r = i then (1 : ℝ) else 0) : Fin (n + 1) → ℝ)
      ).IsTotallyUnimodular := by sorry

end MatousekLP.Integrality
