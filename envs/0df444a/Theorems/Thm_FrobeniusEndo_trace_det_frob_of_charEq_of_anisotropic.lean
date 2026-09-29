-- Prove2me | Theorems.Thm_FrobeniusEndo_trace_det_frob_of_charEq_of_anisotropic
-- name    : FrobeniusEndo.trace_det_frob_of_charEq_of_anisotropic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/0252b24b-21a8-5dbf-b224-69b315048d3f
-- title:
--   Trace and determinant of σ on W(K)[p], anisotropic case
-- statement:
--   Let $R \to S \to K$ be a tower of commutative rings with $K$ a field (the scalar tower $R \to S \to K$ being assumed compatible), let $W$ be a Weierstrass curve over $R$, let $\sigma$ be an $S$-algebra automorphism of $K$, and let $p$ be a prime. Write $T =$ `Submodule.torsionBy ℤ (W⁄K).Point p`, the $p$-torsion of the group of points of the base change of $W$ to $K$ (affine nonsingular points together with the point at infinity), a module over $\mathbb{Z}/p$, and let $M =$ `galoisRepModuleEnd S W p σ` be the $\mathbb{Z}/p$-linear endomorphism of $T$ given by the action of $\sigma$ on points. Assume $\#T = p^{2}$; let $a \in \mathbb{Z}$ and $q \in \mathbb{N}$ be such that $M^{2} - \bar a M + \bar q \,\mathrm{id} = 0$ in $\operatorname{End}_{\mathbb{Z}/p}(T)$, and such that no $c \in \mathbb{Z}/p$ satisfies $c^{2} - \bar a c + \bar q = 0$. Then the trace of $M$ equals $\bar a$ and the determinant of $M$ equals $\bar q$ in $\mathbb{Z}/p$.
--
--   This is the anisotropic half of the passage from a quadratic relation satisfied by a Frobenius-type automorphism on $p$-torsion to the congruences $\operatorname{tr} \equiv a$, $\det \equiv q \pmod p$: when $X^{2} - \bar a X + \bar q$ has no root in $\mathbb{F}_p$, the relation alone pins down trace and determinant, with no input from counting kernels of isogenies $[m] - [n]\sigma$. It is used by [`FrobeniusEndo.trace_det_frob_of_line_of_charEqOnPoints`](thm.html#FrobeniusEndo.trace_det_frob_of_line_of_charEqOnPoints).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusEndo_trace_det_frob_of_charEq_of_anisotropic.lean

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem FrobeniusEndo.trace_det_frob_of_charEq_of_anisotropic {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (a : ℤ) (q : ℕ) (hCE : galoisRepModuleEnd S W p σ * galoisRepModuleEnd S W p σ - (a : ZMod p) • galoisRepModuleEnd S W p σ + (q : ZMod p) • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p)) = 0) (hno : ¬ ∃ c : ZMod p, c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0) : galoisTrace S W p σ = (a : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) := by sorry
