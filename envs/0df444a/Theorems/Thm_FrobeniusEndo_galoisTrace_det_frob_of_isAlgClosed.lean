-- Prove2me | Theorems.Thm_FrobeniusEndo_galoisTrace_det_frob_of_isAlgClosed
-- name    : FrobeniusEndo.galoisTrace_det_frob_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/621e51a5-83b6-527f-99af-f7056ceeb249
-- title:
--   Trace and determinant of Frobenius on p-torsion
-- statement:
--   Let $R$ be a commutative ring, $F$ a finite field, and $k$ a field with decidable equality, equipped with $R$-algebra structures on $F$ and on $k$ and an $F$-algebra structure on $k$ forming a scalar tower over $R$, with $k$ algebraically closed. Let $W$ be a Weierstrass curve over $R$ whose base change $W⁄k$ is elliptic, and let $\sigma : k \simeq_{\mathrm{alg}[F]} k$ be an $F$-algebra automorphism of $k$ satisfying $\sigma(x) = x^{\#F}$ for all $x \in k$; assume moreover that $\#F$ is prime. Let $p$ be a prime (as a `Fact` instance) with $(p : k) \neq 0$. Consider the $p$-torsion submodule $\mathrm{torsionBy}\ \mathbb{Z}\ (W⁄k).\mathrm{Point}\ p$ of the group of affine points of $W⁄k$, viewed as a $\mathbb{Z}/p$-module, and let $\mathrm{galoisRepModuleEnd}\ F\ W\ p\ \sigma$ be the $\mathbb{Z}/p$-linear endomorphism of it given by the action of $\sigma$. The conclusion is the conjunction of two identities in $\mathbb{Z}/p$: the trace of this endomorphism, namely $\mathrm{galoisTrace}\ F\ W\ p\ \sigma$, equals $\#F + 1 - \#(W⁄F).\mathrm{Point}$, and its determinant equals $\#F$.
--
--   This is the statement that geometric Frobenius acting on the $p$-torsion of an elliptic curve over an algebraically closed field of characteristic different from $p$ has trace $a_q = q + 1 - \#W(\mathbb{F}_q)$ and determinant $q$ (the mod-$p$ cyclotomic character), valid for all primes $p$ invertible in $k$, including $p = 2$ and the supersingular case. It feeds, via transport along reduction, into [`WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel_of_card_torsionBy`](thm.html#WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel_of_card_torsionBy), which identifies the trace of Frobenius on the mod-$p$ representation of an elliptic curve with the coefficient $a_\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_galoisTrace_det_frob_of_isAlgClosed.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.galoisTrace_det_frob_of_isAlgClosed {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] [IsAlgClosed k] (W : WeierstrassCurve R) [(W⁄k).IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (hF : (Fintype.card F).Prime) (p : ℕ) [Fact p.Prime] (hpk : (p : k) ≠ 0) : galoisTrace F W p σ = (Fintype.card F : ZMod p) + 1 - (Nat.card (W⁄F).Point : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd F W p σ) = (Fintype.card F : ZMod p) := by sorry
