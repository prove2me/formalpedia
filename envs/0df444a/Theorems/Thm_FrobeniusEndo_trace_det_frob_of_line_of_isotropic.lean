-- Prove2me | Theorems.Thm_FrobeniusEndo_trace_det_frob_of_line_of_isotropic
-- name    : FrobeniusEndo.trace_det_frob_of_line_of_isotropic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/54d1089d-9e39-52f0-806f-b36250fe9e06
-- title:
--   Trace and determinant of σ on p-torsion, isotropic case
-- statement:
--   Let $R \to S \to K$ be a tower of commutative rings with $K$ a field, let $W$ be a Weierstrass curve over $R$, and let $\sigma$ be an $S$-algebra automorphism of $K$, acting on the group $(W\!\restriction_K)$-points $(W⁄K).\mathrm{Point}$ of the base change of $W$ to $K$; write $\mathrm{frobEnd}\,W\,\sigma$ for the additive endomorphism of that group induced by this action. Let $p$ be a prime. Assume the $p$-torsion subgroup $\{P : pP = 0\}$ of $(W⁄K).\mathrm{Point}$ has exactly $p^2$ elements, and that $p \ne 0$ in $K$. Let $a$ be an integer and $q$ a natural number, and assume the two line hypotheses: for every natural number $m$ with $1 \le m \le 2p$ and $m \ne 0$ in $K$, the cardinality $\mathrm{kerDeg}$ of the kernel of $m \cdot \mathrm{id} - \mathrm{frobEnd}\,W\,\sigma$, that is of $\{P : mP = \sigma P\}$, equals $m^2 - am + q$ (as integers, the cardinality being $0$ when the kernel is infinite), and this cardinality is nonzero for all such $m$. Assume finally that $c^2 - \bar a c + \bar q = 0$ for some $c \in \mathbb{Z}/p$. Then the trace over $\mathbb{Z}/p$ of the induced $\mathbb{Z}/p$-linear endomorphism of the $p$-torsion equals $\bar a$, and its determinant equals $\bar q$.
--
--   This is the standard determination of the trace and determinant of a Frobenius-type automorphism on $E[p]$ from the kernel counts $\#\ker([m]-\sigma) = m^2 - am + q$, here in the case where the quadratic $X^2 - \bar aX + \bar q$ already has a root modulo $p$. It feeds the characteristic-polynomial statement [`FrobeniusEndo.charEq_on_torsionBy_of_line_of_isotropic`](thm.html#FrobeniusEndo.charEq_on_torsionBy_of_line_of_isotropic) and the variant [`FrobeniusEndo.trace_det_frob_of_line_of_charEqOnPoints`](thm.html#FrobeniusEndo.trace_det_frob_of_line_of_charEqOnPoints), which remove the isotropy hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_trace_det_frob_of_line_of_isotropic.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.trace_det_frob_of_line_of_isotropic {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) (a : ℤ) (q : ℕ) (hline : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 → ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q) (hpos : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0) (hiso : ∃ c : ZMod p, c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0) : galoisTrace S W p σ = (a : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) := by sorry
