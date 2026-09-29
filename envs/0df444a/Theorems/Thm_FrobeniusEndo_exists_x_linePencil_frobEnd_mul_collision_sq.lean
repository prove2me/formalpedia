-- Prove2me | Theorems.Thm_FrobeniusEndo_exists_x_linePencil_frobEnd_mul_collision_sq
-- name    : FrobeniusEndo.exists_x_linePencil_frobEnd_mul_collision_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f00d7229-dcf6-50af-ac82-30046e1d8e1c
-- title:
--   x([m]P-π P) as a rational function of x(P)
-- statement:
--   Let $R$ be a commutative ring, $F$ a finite field with $q = \#F$ elements, and $k$ an algebraically closed field with decidable equality, forming a tower $R \to F \to k$ of algebras, and let $W$ be a Weierstrass curve over $R$ whose base change $W_{/k}$ is elliptic. Let $\sigma$ be an $F$-algebra automorphism of $k$ with $\sigma(x) = x^{q}$ for all $x \in k$, and let $m$ be an integer such that the set of abscissae $x \in k$ carrying an affine point $(x,y)$ of $W_{/k}$ with $m \cdot (x,y) = 0$ is finite. Then there is a polynomial $U \in k[X]$ with the following two properties. First, if $m \neq 0$ in $k$, then $\deg U = 2|m|^{2} + 2q - 1$. Secondly, let $(x,y)$ and $(x_1,y_1)$ be nonsingular affine points of $W_{/k}$ with $m \cdot (x,y) = (x_1,y_1)$, and suppose that the division polynomials $\Psi_m^{2}$, the collision polynomial $\Phi_m - X^{q}\Psi_m^{2}$, and $\Psi_2^{2}$ of $W_{/k}$ all have nonzero value at $x$. Then the image of $(x,y)$ under the endomorphism $m \cdot \mathrm{id} - \mathrm{frobEnd}$ of $W_{/k}(k)$, where $\mathrm{frobEnd}$ is the additive endomorphism given by the action of $\sigma$ on points, is nonzero; and whenever that image is the affine point $(x',y')$, one has $x' \cdot \bigl((\Phi_m - X^{q}\Psi_m^{2})(x)\bigr)^{2} = U(x)$.
--
--   This is the rationality and degree statement underlying Manin's elementary proof of the Hasse bound: the abscissa of $[m]P - \pi P$, multiplied by the square of the collision polynomial $\Phi_m - X^{q}\Psi_m^{2}$, is a polynomial in $x(P)$ of degree $2m^{2} + 2q - 1$. It feeds the computation of the degree of $\ker([m] - \pi)$, in the form used by [`FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_finiteField`](thm.html#FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_finiteField) and [`FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_of_torsion`](thm.html#FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_of_torsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_exists_x_linePencil_frobEnd_mul_collision_sq.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.exists_x_linePencil_frobEnd_mul_collision_sq {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] [IsAlgClosed k] (W : WeierstrassCurve R) [(W⁄k).IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (m : ℤ) (hfin : {x : k | ∃ (y : k) (h : (W⁄k).Nonsingular x y), m • Point.some x y h = 0}.Finite) : ∃ U : Polynomial k, ((m : k) ≠ 0 → U.natDegree = 2 * m.natAbs ^ 2 + 2 * Fintype.card F - 1) ∧ ∀ {x y : k} (h : (W⁄k).Nonsingular x y) {x₁ y₁ : k} (h₁ : (W⁄k).Nonsingular x₁ y₁), m • Point.some x y h = Point.some x₁ y₁ h₁ → ((W⁄k).ΨSq m).eval x ≠ 0 → ((W⁄k).Φ m - Polynomial.X ^ Fintype.card F * (W⁄k).ΨSq m).eval x ≠ 0 → (W⁄k).Ψ₂Sq.eval x ≠ 0 → linePencil (frobEnd W σ) m 1 (Point.some x y h) ≠ 0 ∧ ∀ {x' y' : k} (h' : (W⁄k).Nonsingular x' y'), linePencil (frobEnd W σ) m 1 (Point.some x y h) = Point.some x' y' h' → x' * ((W⁄k).Φ m - Polynomial.X ^ Fintype.card F * (W⁄k).ΨSq m).eval x ^ 2 = U.eval x := by sorry
