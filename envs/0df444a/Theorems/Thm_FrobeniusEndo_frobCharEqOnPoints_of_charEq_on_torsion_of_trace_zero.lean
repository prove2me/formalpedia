-- Prove2me | Theorems.Thm_FrobeniusEndo_frobCharEqOnPoints_of_charEq_on_torsion_of_trace_zero
-- name    : FrobeniusEndo.frobCharEqOnPoints_of_charEq_on_torsion_of_trace_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/2dd30633-f8c1-5409-85ad-47dc9b7594f9
-- title:
--   Frobenius characteristic equation on points, trace-zero case
-- statement:
--   Let $R$ be a commutative ring, $F$ a finite field, $k$ a field, and suppose $F$ and $k$ are $R$-algebras, $k$ an $F$-algebra, the three structures forming a scalar tower; write $q = \operatorname{card} F$. Let $W$ be a Weierstrass curve over $R$ and let $\sigma$ be an $F$-algebra automorphism of $k$ with $\sigma(x) = x^{q}$ for every $x \in k$, acting on the group $(W\!⁄k).\mathrm{Point}$ of points of the base change of $W$ to $k$ through the associated scalar action. Assume that for every natural number $N$ there is a prime $r > N$ such that the $\mathbb{Z}$-submodule of $r$-torsion points of $(W\!⁄k).\mathrm{Point}$ has exactly $r^{2}$ elements and such that every $P$ with $r \cdot P = 0$ satisfies $\sigma\cdot(\sigma\cdot P) + q\cdot P = 0$. The conclusion is `FrobCharEqOnPoints W σ 0 q`, that is, $\sigma\cdot(\sigma\cdot P) - 0\cdot(\sigma\cdot P) + q\cdot P = 0$ for every point $P$ of $(W\!⁄k).\mathrm{Point}$.
--
--   This is the trace-zero branch of the assertion that the $q$-power Frobenius satisfies its characteristic equation $X^{2} - aX + q$ pointwise on the $k$-points of a Weierstrass curve, obtained by passing from cofinally many full $r$-torsion subgroups to all points. It is used in the proof of [`FrobeniusEndo.frobCharEqOnPoints_of_line`](thm.html#FrobeniusEndo.frobCharEqOnPoints_of_line), where the torsion hypothesis is supplied by a count of the kernels of $m - \pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_frobCharEqOnPoints_of_charEq_on_torsion_of_trace_zero.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.frobCharEqOnPoints_of_charEq_on_torsion_of_trace_zero {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (hkill : ∀ N : ℕ, ∃ r : ℕ, N < r ∧ r.Prime ∧ Nat.card (Submodule.torsionBy ℤ (W⁄k).Point r) = r ^ 2 ∧ ∀ P : (W⁄k).Point, (r : ℤ) • P = 0 → σ • (σ • P) + (Fintype.card F : ℤ) • P = 0) : FrobCharEqOnPoints W σ 0 (Fintype.card F) := by sorry
