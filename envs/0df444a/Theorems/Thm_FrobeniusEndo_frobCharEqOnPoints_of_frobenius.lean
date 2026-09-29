-- Prove2me | Theorems.Thm_FrobeniusEndo_frobCharEqOnPoints_of_frobenius
-- name    : FrobeniusEndo.frobCharEqOnPoints_of_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/fec843be-6909-5c6e-93ce-0bb605f7b389
-- title:
--   Frobenius satisfies π²-aπ+q=0 on all k-points
-- statement:
--   Let $R$ be a commutative ring, $F$ a finite field, and $k$ an algebraically closed field, equipped with $R$-algebra structures on $F$ and $k$ and an $F$-algebra structure on $k$ forming a scalar tower over $R$. Let $W$ be a Weierstrass curve over $R$ whose base change $W⁄k$ to $k$ is elliptic, and let $\sigma : k \simeq_{\mathrm{alg}[F]} k$ be an $F$-algebra automorphism of $k$ which is the $q$-power map, $\sigma x = x^{q}$ for all $x \in k$, where $q = \#F$; assume moreover that $q$ is prime. Then `FrobCharEqOnPoints W σ a q` holds with $a = q + 1 - \#(W⁄F).\mathrm{Point}$ (the cardinality of the group of points of the base change of $W$ to $F$, as an integer) and with $q = \#F$: that is, for every point $P$ of the elliptic curve $W⁄k$ over $k$,
--   $$\sigma \bullet (\sigma \bullet P) - a \bullet (\sigma \bullet P) + q \bullet P = 0,$$
--   where $\sigma \bullet$ denotes the induced action of $\sigma$ on points and the integer multiples are taken in the group $(W⁄k).\mathrm{Point}$. Thus Frobenius satisfies the relation $\pi^{2} - a\pi + q = 0$ pointwise on $(W⁄k).\mathrm{Point}$.
--
--   This is the pointwise form of the statement that the characteristic polynomial of the Frobenius endomorphism of an elliptic curve over a finite field $\mathbb{F}_q$ is $X^{2} - aX + q$ with $a = q + 1 - \#E(\mathbb{F}_q)$, here under the restriction that $q$ is prime. It feeds the computation of the trace and determinant of Frobenius on torsion, via [`FrobeniusEndo.galoisTrace_det_frob_of_isAlgClosed`](thm.html#FrobeniusEndo.galoisTrace_det_frob_of_isAlgClosed) and [`WeierstrassCurve.frobenius_cayleyHamilton_on_torsion`](thm.html#WeierstrassCurve.frobenius_cayleyHamilton_on_torsion), which is the special-fibre input needed for the Galois representation attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_frobCharEqOnPoints_of_frobenius.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.frobCharEqOnPoints_of_frobenius {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] [IsAlgClosed k] (W : WeierstrassCurve R) [(W⁄k).IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (hF : (Fintype.card F).Prime) : FrobCharEqOnPoints W σ ((Fintype.card F : ℤ) + 1 - (Nat.card (W⁄F).Point : ℤ)) (Fintype.card F) := by sorry
