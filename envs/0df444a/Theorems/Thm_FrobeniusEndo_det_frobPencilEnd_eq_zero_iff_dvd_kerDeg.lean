-- Prove2me | Theorems.Thm_FrobeniusEndo_det_frobPencilEnd_eq_zero_iff_dvd_kerDeg
-- name    : FrobeniusEndo.det_frobPencilEnd_eq_zero_iff_dvd_kerDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a3aa1ea4-c840-55bc-ab5b-e662f9e8a3cc
-- title:
--   Vanishing of det(̄ m-̄ nσ) on p-torsion versus p∣#ker
-- statement:
--   Let $R$, $S$ be commutative rings and $K$ a field, with algebra structures making $R\to S\to K$ a scalar tower, let $W$ be a Weierstrass curve over $R$, let $\sigma$ be an $S$-algebra automorphism of $K$, and let $p$ be a prime. Write $(W\!\downharpoonright\!K)$ for the base change of $W$ to $K$ and $(W\!\downharpoonright\!K).\mathrm{Point}$ for its group of $K$-points; $\sigma$ acts on this group, and `frobEnd W σ` is the resulting additive endomorphism. For integers $m,n$, `kerDeg (frobEnd W σ) m n` is the cardinality (in the sense of `Nat.card`, hence $0$ for an infinite set) of the kernel of the additive endomorphism $m\cdot\mathrm{id}-n\cdot\sigma$ of $(W\!\downharpoonright\!K).\mathrm{Point}$, and `frobPencilEnd W σ p m n` is the $\mathbb{Z}/p$-linear endomorphism $\bar m\cdot 1-\bar n\cdot\rho(\sigma)$ of the $p$-torsion submodule $\{P: p\cdot P=0\}$, where $\rho(\sigma)$ is the endomorphism induced by the action of $\sigma$. Assume the $p$-torsion submodule has nonzero `Nat.card` (i.e. is finite) and that $\mathrm{kerDeg}(\mathrm{frobEnd}\ W\ \sigma)\ m\ n\neq 0$. Then $\det(\bar m\cdot1-\bar n\cdot\rho(\sigma))=0$ if and only if $p$ divides $\mathrm{kerDeg}(\mathrm{frobEnd}\ W\ \sigma)\ m\ n$.
--
--   This is the dictionary between the kernel counts $\#\ker(m-n\sigma)$ on $K$-points and the eigenvalues of $\sigma$ on the $p$-torsion: $\bar m/\bar n$ is an eigenvalue of the mod $p$ Galois representation exactly when $p$ divides the kernel count. It is used in the computation of the trace and determinant of Frobenius on $p$-torsion from kernel degrees, via [`FrobeniusEndo.trace_det_frob_of_line_of_isotropic`](thm.html#FrobeniusEndo.trace_det_frob_of_line_of_isotropic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_det_frobPencilEnd_eq_zero_iff_dvd_kerDeg.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.det_frobPencilEnd_eq_zero_iff_dvd_kerDeg {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfin : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) ≠ 0) {m n : ℤ} (hpos : kerDeg (frobEnd W σ) m n ≠ 0) : LinearMap.det (frobPencilEnd W σ p m n) = 0 ↔ p ∣ kerDeg (frobEnd W σ) m n := by sorry
