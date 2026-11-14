-- Prove2me | Theorems.Thm_LatticePrepro_pow_X_sub_C_dvd_det
-- name    : LatticePrepro.pow_X_sub_C_dvd_det
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:24:52.088137+00:00
-- url     : https://prove2.me/theorems/536ddb54-c2b3-4612-8262-e88fe49873d2
-- title:
--   Rank deficiency at a point divides the determinant of a polynomial matrix
-- statement:
--   Let $\mathbb S$ be a field, $n$ a finite index set, and $M(X) \in \mathbb S[X]^{n \times n}$ a square matrix of polynomials. For $s \in \mathbb S$, write $M(s) \in \mathbb S^{n\times n}$ for the matrix obtained by evaluating every entry at $s$. Then the rank deficiency of $M(s)$ bounds the multiplicity of $s$ as a root of $\det M(X)$:
--   $$(X - s)^{\,|n| - \operatorname{rank} M(s)} \ \Big|\ \det M(X) \qquad \text{in } \mathbb S[X],$$
--   where $|n|$ is the number of rows and the rank is taken over $\mathbb S$.
--
--   This is the divisibility step in the proof of Lemma A.6 (as in Fancsali–Sziklai). It is applied to a nonsingular square submatrix of the polynomial matrix of an evaluation table; since the factors $X - s$ for distinct $s \in \mathbb S$ are coprime, the total rank deficiency over all sample points is at most the degree of the determinant, which yields the weight bound of Lemma A.6.
--
--   **Formalization Note**: $M(s)$ is `M.map (eval s)` and $X - s$ is `X - C s`. The exponent uses natural-number subtraction, which never truncates because $\operatorname{rank} M(s) \le |n|$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in the proof of Lemma A.6 (\label{lem:table-rank}); Lean: LatticePrepro/Basic/Matrix.lean, LatticePrepro.pow_X_sub_C_dvd_det

import Mathlib

open Polynomial Matrix
variable {𝕊 : Type*} [Field 𝕊] {n : Type*} [Fintype n] [DecidableEq n]

theorem LatticePrepro.pow_X_sub_C_dvd_det (M : Matrix n n 𝕊[X]) (s : 𝕊) :
    (X - C s) ^ (Fintype.card n - (M.map (eval s)).rank) ∣ M.det := by sorry
