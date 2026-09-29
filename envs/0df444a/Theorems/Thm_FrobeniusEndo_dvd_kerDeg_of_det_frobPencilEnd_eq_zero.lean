-- Prove2me | Theorems.Thm_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero
-- name    : FrobeniusEndo.dvd_kerDeg_of_det_frobPencilEnd_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/5a10417c-da45-5279-9d83-dc69611125a6
-- title:
--   Singular pencil on p-torsion forces p ∣ #ker([m]-[n]σ)
-- statement:
--   Let $R$ and $S$ be commutative rings and $K$ a field with decidable equality, equipped with $R$-algebra structures on $S$ and $K$ and an $S$-algebra structure on $K$ forming a scalar tower; let $W$ be a Weierstrass curve over $R$, let $\sigma$ be an $S$-algebra automorphism of $K$, and let $p$ be a natural number assumed prime. Write $(W⁄K).\mathrm{Point}$ for the group of points of the base change of $W$ to $K$, on which $\sigma$ acts; let $T = \mathrm{Submodule.torsionBy}\ \mathbb{Z}\ (W⁄K).\mathrm{Point}\ p$ be the subgroup of points killed by $p$, viewed as a $\mathbb{Z}/p$-module, and let `galoisRepModuleEnd` be the $\mathbb{Z}/p$-linear endomorphism of $T$ induced by the action of $\sigma$. For integers $m, n$, the hypothesis is that the determinant of the $\mathbb{Z}/p$-linear endomorphism $\bar m \cdot 1 - \bar n \cdot \mathrm{galoisRepModuleEnd}(\sigma)$ of $T$ vanishes (by Mathlib's convention this determinant is $1$ unless $T$ is finite and free, so the hypothesis also constrains $T$). The conclusion is that $p$ divides $\mathrm{kerDeg}$ of the $\sigma$-action at $(m,n)$, namely $\mathrm{Nat.card}$ of the kernel of the additive endomorphism $m \cdot \mathrm{id} - n \cdot (P \mapsto \sigma \cdot P)$ of $(W⁄K).\mathrm{Point}$, this cardinality being $0$ when the kernel is infinite.
--
--   This is the forward half of the dictionary between the $\mathbb{F}_p$-spectrum of a Galois automorphism acting on the $p$-torsion and the kernel counts $\#\ker([m]-[n]\sigma)$, the counts through which the trace of Frobenius is read off modulo $p$. It is used in the equivalence [`FrobeniusEndo.det_frobPencilEnd_eq_zero_iff_dvd_kerDeg`](thm.html#FrobeniusEndo.det_frobPencilEnd_eq_zero_iff_dvd_kerDeg) and in [`FrobeniusEndo.trace_det_frob_of_line_of_isotropic`](thm.html#FrobeniusEndo.trace_det_frob_of_line_of_isotropic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.dvd_kerDeg_of_det_frobPencilEnd_eq_zero {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] {m n : ℤ} (h : LinearMap.det (frobPencilEnd W σ p m n) = 0) : p ∣ kerDeg (frobEnd W σ) m n := by sorry
