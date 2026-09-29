-- Prove2me | Theorems.Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_finiteField
-- name    : FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_finiteField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/0a63ba96-25d3-5a69-9dac-a5316bcc866b
-- title:
--   Kernel count of [m]-π over a finite field
-- statement:
--   Let $R$ be a commutative ring, $F$ a finite field, and $k$ an algebraically closed field, with $R$-algebra structures on $F$ and $k$ and an $F$-algebra structure on $k$ forming a scalar tower. Let $W$ be a Weierstrass curve over $R$ whose base change $W_{/k}$ to $k$ is elliptic, and let $\sigma$ be an $F$-algebra automorphism of $k$ such that $\sigma(x)=x^{\#F}$ for all $x\in k$; write $\pi=$ `frobEnd W σ` for the endomorphism of the additive group $(W_{/k})(k)$ of affine points induced by the action of $\sigma$. For integers $m,n$, `kerDeg` $(\pi,m,n)$ denotes $\mathrm{Nat.card}$ of the kernel of the additive endomorphism $m\cdot\mathrm{id}-n\cdot\pi$ of $(W_{/k})(k)$ (hence $0$ if that kernel is infinite). Then for every natural number $m$ with $1\le m$ whose image in $k$ is nonzero, the cardinality $d(m):=$ `kerDeg` $(\pi,m,1)$ of $\ker([m]-\pi)$ is strictly positive, and, as an identity of integers,
--   $$d(m)=m^2-\bigl(\#F+1-d(1)\bigr)m+\#F,$$
--   where $d(1)$ is the cardinality of $\ker(\mathrm{id}-\pi)$.
--
--   This is the kernel-count identity for the pencil $[m]-\pi$ on an elliptic curve over a finite field with $\#F$ elements — classically the statement that $\deg([m]-\pi)=m^2-am+\#F$ with $a=\#F+1-\#W(F)$, in the elementary form used in Manin's proof of Hasse's theorem — stated here for an arbitrary finite field rather than a prime field. It is used to identify the trace of Frobenius on the Tate module, in [`WeierstrassCurve.trace_frobenius_tateModule_eq_card_add_one_sub`](thm.html#WeierstrassCurve.trace_frobenius_tateModule_eq_card_add_one_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_finiteField.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_finiteField {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] [IsAlgClosed k] (W : WeierstrassCurve R) [(W⁄k).IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (m : ℕ) (hm : 1 ≤ m) (hmk : (m : k) ≠ 0) : 0 < kerDeg (frobEnd W σ) m 1 ∧ ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - ((Fintype.card F : ℤ) + 1 - kerDeg (frobEnd W σ) 1 1) * m + Fintype.card F := by sorry
