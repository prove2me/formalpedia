-- Prove2me | Theorems.Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_of_torsion
-- name    : FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_of_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/675ebf6f-69f9-55b3-adef-4ca67b02e463
-- title:
--   Kernel count #ker([m]-π)=m²-am+q for the Frobenius pencil
-- statement:
--   Let $R$ be a commutative ring, $F$ a finite field, $k$ an algebraically closed field, with algebra maps $R \to F \to k$ forming a scalar tower, and let $W$ be a Weierstrass curve over $R$ whose base change $W_{/k}$ is elliptic. Let $\sigma$ be an $F$-algebra automorphism of $k$ with $\sigma(x) = x^{q}$ for all $x \in k$, where $q = \#F$, and assume $q$ is prime. Two division-polynomial facts are assumed as hypotheses: `htor`, that for every $n \in \mathbb{Z}$ and every nonsingular affine point $(x,y)$ of $W_{/k}$ with $n \cdot (x,y) = 0$ one has $\Psi_n^2(x) = 0$; and `hcop`, that $\Phi_n$ and $\Psi_n^2$ are coprime for every $n \in \mathbb{Z}$. Finally let $m$ be a natural number with $m \ge 1$ whose image in $k$ is nonzero. Writing $\pi$ for the endomorphism `frobEnd` of the group $(W_{/k})(k)$ induced by $\sigma$, and $\mathrm{kerDeg}(\pi, a, b) = \#\ker(a - b\pi)$ as the cardinality of the kernel of $a \cdot \mathrm{id} - b\pi$, the conclusion is that $\#\ker([m] - \pi) > 0$ and, as an identity of integers, $$\#\ker([m]-\pi) = m^2 - \bigl(q + 1 - \#\ker([1]-\pi)\bigr)m + q.$$
--
--   This is the degree formula at the heart of Manin's elementary proof of the Hasse bound, with the trace written as $a = q + 1 - \#\ker(1-\pi)$ rather than through a point count. It is the version carrying the two division-polynomial inputs as explicit hypotheses; the hypothesis-free form [`FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq`](thm.html#FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq) is obtained from it by discharging them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_of_torsion.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_of_torsion {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] [IsAlgClosed k] (W : WeierstrassCurve R) [(W⁄k).IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (hF : (Fintype.card F).Prime) (htor : ∀ (n : ℤ) {x y : k} (h : (W⁄k).Nonsingular x y), n • Point.some x y h = 0 → ((W⁄k).ΨSq n).eval x = 0) (hcop : ∀ n : ℤ, IsCoprime ((W⁄k).Φ n) ((W⁄k).ΨSq n)) (m : ℕ) (hm : 1 ≤ m) (hmk : (m : k) ≠ 0) : 0 < kerDeg (frobEnd W σ) m 1 ∧ ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - ((Fintype.card F : ℤ) + 1 - kerDeg (frobEnd W σ) 1 1) * m + Fintype.card F := by sorry
