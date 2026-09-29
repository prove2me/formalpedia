-- Prove2me | Theorems.Thm_FrobeniusEndo_trace_det_frob_of_line_of_charEqOnPoints
-- name    : FrobeniusEndo.trace_det_frob_of_line_of_charEqOnPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/facb776f-8673-506b-99db-6f4af626bdc3
-- title:
--   Trace and determinant of σ on W(K)[p]
-- statement:
--   Let $R$, $S$ be commutative rings and $K$ a field with decidable equality, equipped with $R$-algebra, $R\to K$ and $S\to K$ structures forming a scalar tower $R\to S\to K$; let $W$ be a Weierstrass curve over $R$, let $\sigma$ be an $S$-algebra automorphism of $K$ (acting on the group $(W_{/K})(K)$ of affine nonsingular points together with the point at infinity), and let $p$ be a natural number assumed prime. Assume: the $p$-torsion subgroup $\{P : p\cdot P = 0\}$ of $(W_{/K})(K)$ has cardinality exactly $p^2$; $p \neq 0$ in $K$. Let $a$ be an integer and $q$ a natural number such that, for every natural $m \geq 1$ with $m \neq 0$ in $K$, the number of points $P$ with $mP - \sigma P = 0$ (the cardinality of the kernel of $m\cdot\mathrm{id} - \sigma$ on $(W_{/K})(K)$, taken as a natural number) equals $m^2 - am + q$, and this number is nonzero; assume further the pointwise identity $\sigma(\sigma P) - a\,\sigma P + q\,P = 0$ for all $P \in (W_{/K})(K)$. Then the $\mathbb{Z}/p$-linear endomorphism of the $p$-torsion module induced by $\sigma$ has trace $a \bmod p$ and determinant $q \bmod p$.
--
--   This is the Eichler–Shimura-type congruence in its elementary form: on the $p$-torsion of a Weierstrass curve, the matrix of the automorphism $\sigma$ has trace $\equiv a$ and determinant $\equiv q \pmod p$, the classical case being $\sigma$ the $q$-power Frobenius of an elliptic curve over a finite field with $a = q+1-\#E(\mathbb{F}_q)$. It feeds the determination of the mod $p$ Galois representation attached to an elliptic curve, and is used directly by [`FrobeniusEndo.galoisTrace_frob_eq_of_line_of_charEqOnPoints`](thm.html#FrobeniusEndo.galoisTrace_frob_eq_of_line_of_charEqOnPoints).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_trace_det_frob_of_line_of_charEqOnPoints.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.trace_det_frob_of_line_of_charEqOnPoints {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) (a : ℤ) (q : ℕ) (hline : ∀ m : ℕ, 1 ≤ m → (m : K) ≠ 0 → ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q) (hpos : ∀ m : ℕ, 1 ≤ m → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0) (hpt : FrobCharEqOnPoints W σ a q) : galoisTrace S W p σ = (a : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) := by sorry
