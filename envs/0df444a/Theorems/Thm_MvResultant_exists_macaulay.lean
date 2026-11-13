-- Prove2me | Theorems.Thm_MvResultant_exists_macaulay
-- name    : MvResultant.exists_macaulay
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T19:08:24.171708+00:00
-- url     : https://prove2.me/theorems/d5d38f18-ee44-4bfe-a54e-08d7373d978c
-- title:
--   Macaulay's determinant: a multiple of the resultant restricting to $t^M$, $M\le\prod_{j\ne i}D_j$, on the diagonal line
-- statement:
--   Let $n\ge1$ and $D_1,\dots,D_n\ge1$. Consider $n$ homogeneous forms $F_j=\sum_{|\alpha|=D_j}u_{j,\alpha}x^\alpha$ in $n$ variables with indeterminate coefficients $u_{j,\alpha}$. Fix $i\in[n]$.
--
--   **Statement.** There is a polynomial $Q\in\mathbb{C}[u_{j,\alpha}]$ with two properties:
--   1. $Q$ vanishes at the coefficient vector of every system $(F_1,\dots,F_n)$ that has a common nonzero zero in $\mathbb{C}^n$;
--   2. on the *diagonal line* $\big(x_1^{D_1},\dots,t\,x_i^{D_i},\dots,x_n^{D_n}\big)$, $Q$ restricts to $t^{M}$ for some $M\le\prod_{j\ne i}D_j$.
--
--   **The intended witness is Macaulay's determinant.** Put $D=\sum_j(D_j-1)+1$, and index rows and columns by the monomials $x^\beta$ of degree $D$:
--   - each row monomial $x^\beta$ is assigned to the first form $F_j$ with $x_j^{D_j}\mid x^\beta$, scanning the indices $j\ne i$ first and taking $j=i$ last;
--   - the row lists the coefficients of $(x^\beta/x_j^{D_j})\,F_j$.
--
--   The two properties then hold as follows:
--   - **Vanishing:** if $p\ne0$ is a common zero, the vector $(p^\gamma)_\gamma$ is a nonzero kernel vector, so $\det=0$.
--   - **Restriction:** on the diagonal line the matrix is diagonal, with entry $t$ on the rows assigned to $F_i$ and $1$ elsewhere. Those rows are the monomials with $\beta_j<D_j$ for all $j\neq i$, and there are at most $\prod_{j\ne i}D_j$ of them.
--
--   Combined with divisibility from the Nullstellensatz, this bounds the block degree of the resultant: `MvResultant.blockDegree_le`.
-- source:
--   F. S. Macaulay, Some formulae in elimination, Proc. London Math. Soc. 35 (1902) 3–27; Cox–Little–O'Shea, Using Algebraic Geometry, Ch. 3 §4 (Macaulay's formula); Gelfand–Kapranov–Zelevinsky, Ch. 13.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper

namespace MvResultant

theorem exists_macaulay {n : ℕ} {D : Fin n → ℕ} (hD : ∀ j, 1 ≤ D j) (i : Fin n) :
    ∃ Q : MvPolynomial (ResVar n D) ℂ,
      (∀ F : Fin n → MvPolynomial (Fin n) ℂ, (∀ j, (F j).IsHomogeneous (D j)) →
        (∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ j, MvPolynomial.eval x (F j) = 0) →
        MvPolynomial.aeval (fun v : ResVar n D => MvPolynomial.coeff v.2.1 (F v.1)) Q = 0) ∧
      ∃ M ≤ ∏ j ∈ Finset.univ.erase i, D j,
        MvPolynomial.aeval (fun v : ResVar n D =>
          if v.2.1 = Finsupp.single v.1 (D v.1) then
            (if v.1 = i then (Polynomial.X : Polynomial ℂ) else 1) else 0) Q =
          Polynomial.X ^ M := by sorry

end MvResultant
