-- Prove2me | Theorems.Thm_FrobeniusEndo_kerDeg_frobEnd_one_one
-- name    : FrobeniusEndo.kerDeg_frobEnd_one_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f80fdb69-f763-5aae-bae4-cbef67a52b76
-- title:
--   Fixed points of the q-power Frobenius are the F-rational points
-- statement:
--   Let $R$ be a commutative ring, $F$ a finite field, $k$ a field, and suppose $F$ and $k$ are $R$-algebras, $k$ an $F$-algebra, with the scalar tower condition relating the three structure maps. Let $W$ be a Weierstrass curve over $R$ and let $\sigma$ be an $F$-algebra automorphism of $k$ satisfying $\sigma(x) = x^{\#F}$ for every $x \in k$. Write $(W\!\mathbin{/}k).\mathrm{Point}$ for the group of points of the affine curve obtained from $W$ by base change to $k$ (the point at infinity together with the nonsingular affine solutions), and let `frobEnd W σ` be the additive endomorphism of this group induced by the coordinatewise action of $\sigma$. Then the number `kerDeg (frobEnd W σ) 1 1`, defined as $\mathrm{Nat.card}$ of the kernel of the endomorphism $1 \cdot \mathrm{id} - 1 \cdot \mathrm{frobEnd}$, equals $\mathrm{Nat.card}$ of $(W\!\mathbin{/}F).\mathrm{Point}$, the group of points of the base change of $W$ to $F$. No nonsingularity hypothesis on $W$ is imposed; both sides count the point at infinity.
--
--   This is the classical identity $E(\mathbb{F}_q) = \ker(1 - \pi_q)$ on the $k$-points of a curve over a finite field: the points fixed by the $q$-power Frobenius are exactly those with coordinates in $\mathbb{F}_q$. It serves as the $m = 1$ anchor for the computation of $\#\ker(m - \pi)$ in the pencil $m \cdot \mathrm{id} - n \cdot \pi$, and is used downstream in the identification of the trace of Frobenius on the Tate module with $\#F + 1 - \#(W\!\mathbin{/}F).\mathrm{Point}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_kerDeg_frobEnd_one_one.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.FieldTheory.Finite.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.kerDeg_frobEnd_one_one {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) : kerDeg (frobEnd W σ) 1 1 = Nat.card (W⁄F).Point := by sorry
