-- Prove2me | Theorems.Thm_Matrix_charpolyRev_of_transpose_mul_mul_eq_smul
-- name    : Matrix.charpolyRev_of_transpose_mul_mul_eq_smul
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:44:07.393952+00:00
-- url     : https://prove2.me/theorems/93cfc061-2ef2-4c03-b6b1-68b643cd6b8a
-- title:
--   Characteristic polynomials of endomorphisms adjoint under a perfect pairing: $\det\Phi\cdot\det(1-T\Psi)=(-1)^r\chi_\Phi(\lambda T)$
-- statement:
--   Let $K$ be a field, let $\Phi$ be an $r\times r$ matrix and $\Psi$ an $s\times s$ matrix over $K$, and let $G$ be an $r\times s$ matrix that has a two-sided inverse $H$. Thus $r=s$, and the bilinear pairing $\langle x,y\rangle=x^{\mathsf T}Gy$ on $K^r\times K^s$ is perfect. Let $\lambda\in K$ be nonzero and suppose that
--
--   $$
--   \Phi^{\mathsf T}\,G\,\Psi=\lambda\,G,
--   $$
--
--   that is, $\langle\Phi x,\Psi y\rangle=\lambda\,\langle x,y\rangle$ for all $x$ and $y$. Write $\chi_\Phi(T)=\det(T-\Phi)$ for the characteristic polynomial of $\Phi$. Then:
--
--   1. $\det\Phi\neq0$;
--   2. $\det\Phi\cdot\det\Psi=\lambda^{r}$;
--   3. in the polynomial ring $K[T]$,
--   $$
--   \det\Phi\cdot\det(1-T\Psi)=(-1)^{r}\,\chi_\Phi(\lambda T).
--   $$
--
--   Since $\chi_\Phi(\lambda T)=(\lambda T)^{r}\det\big(1-\tfrac{1}{\lambda T}\Phi\big)$, item 3 is the identity
--
--   $$
--   \det(1-T\Psi)=\frac{(-1)^{r}\lambda^{r}T^{r}}{\det\Phi}\,\det\Big(1-\frac{1}{\lambda T}\,\Phi\Big)
--   $$
--
--   of the source, and item 2 is its second assertion $\det\Psi=\lambda^{r}/\det\Phi$.
--
--   This is the linear-algebra step that turns Poincaré duality into the functional equation of a zeta function. When $\Phi$ and $\Psi$ are the matrices of Frobenius on $H^i$ and $H^{2n-i}$ and $\lambda=q^n$, it says that the inverse roots of $\det(1-T\Psi)$ are the numbers $q^n/\alpha$, for $\alpha$ an inverse root of $\det(1-T\Phi)$.
--
--   **Formalization Note** The pairing is given by its Gram matrix `G : Matrix m n K` together with an explicit two-sided inverse `H`, for arbitrary finite index types `m` and `n`. The polynomial $\det(1-T\Psi)$ is Mathlib's `Matrix.charpolyRev Ψ`, the polynomial $\chi_\Phi(\lambda T)$ is `Φ.charpoly.comp (C lam * X)`, and $r$ is `Fintype.card m`. The hypothesis $\lambda\neq0$ is implicit in the source, whose formula divides by $\det\Phi$; without it $\Phi$ need not be invertible.
-- source:
--   R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer (1977), Appendix C (The Weil Conjectures), §4, Lemma 4.3 (endomorphisms $f$, $g$ compatible with a perfect pairing up to the scalar $\lambda$).

import Mathlib

theorem Matrix.charpolyRev_of_transpose_mul_mul_eq_smul {K : Type*} [Field K] {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (Φ : Matrix m m K) (Ψ : Matrix n n K) (G : Matrix m n K) (H : Matrix n m K)
    (hGH : G * H = 1) (hHG : H * G = 1) (lam : K) (hlam : lam ≠ 0)
    (h : Φ.transpose * G * Ψ = lam • G) :
    Φ.det ≠ 0 ∧ Φ.det * Ψ.det = lam ^ Fintype.card m ∧
    Polynomial.C Φ.det * Ψ.charpolyRev =
      (-1) ^ Fintype.card m * Φ.charpoly.comp (Polynomial.C lam * Polynomial.X) := by sorry
