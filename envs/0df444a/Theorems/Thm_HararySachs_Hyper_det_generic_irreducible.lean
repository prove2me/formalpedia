-- Prove2me | Theorems.Thm_HararySachs_Hyper_det_generic_irreducible
-- name    : HararySachs.Hyper.det_generic_irreducible
-- status  : Open
-- author  : @milia
-- created : 2026-11-13T05:20:29.103751+00:00
-- url     : https://prove2.me/theorems/3af0008b-7d54-40b3-b4fb-3dff15daae05
-- title:
--   The generic determinant is irreducible
-- statement:
--   Let $K$ be a field and $n \ge 1$. Let $X = (X_{ij})_{i,j=1}^n$ be a matrix of independent indeterminates. Then $\det X$ is an irreducible element of the polynomial ring $K[X_{ij}]$.
--
--   A standard proof goes by induction on $n$. Write $\det X = a\,X_{11} + b$, where $a$ is the complementary minor and $a$, $b$ do not involve $X_{11}$. By induction $a$ is irreducible. Moreover $a \nmid \det X$: at the permutation matrix of the transposition $(1\,2)$ we have $a = 0$ but $\det = -1$. A polynomial of degree $1$ in one variable whose coefficients have no common factor is irreducible.
--
--   **Formalization Note** The ring is `MvPolynomial (Fin n × Fin n) K` and the matrix is `Matrix.of fun i j => X (i, j)`.
-- source:
--   Classical; e.g. Bôcher, Introduction to Higher Algebra, §61. Used in mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and d6dcd7bc-30eb-4f12-bbe1-a5cdf67294f9.

import Mathlib

namespace HararySachs.Hyper

/-- The determinant of the generic `n × n` matrix is irreducible. -/
theorem det_generic_irreducible (K : Type*) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (Matrix.det (Matrix.of fun i j : Fin n =>
      (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) K))) := by
  sorry

end HararySachs.Hyper
