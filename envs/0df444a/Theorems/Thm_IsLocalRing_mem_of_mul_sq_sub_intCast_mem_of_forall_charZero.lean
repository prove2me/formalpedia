-- Prove2me | Theorems.Thm_IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero
-- name    : IsLocalRing.mem_of_mul_sq_sub_intCast_mem_of_forall_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/577c5a43-e535-5022-9215-779f30299c6a
-- title:
--   Vanishing of r at every prime of a local ring
-- statement:
--   Let $R$ be a commutative local ring, let $r \in R$ and let $d \in \mathbb{Z}$, with $(d : R)$ denoting the image of $d$ under the canonical map $\mathbb{Z} \to R$. Assume three things: $r$ lies in the maximal ideal of $R$; for every prime ideal $\mathfrak{p}$ of $R$ the element $r\,(r^{2} - (d:R))$ lies in $\mathfrak{p}$; and for every prime ideal $\mathfrak{p}$ of $R$ whose quotient $R/\mathfrak{p}$ has characteristic zero, $r$ lies in $\mathfrak{p}$. Then for every prime ideal $\mathfrak{p}$ of $R$ one has $r \in \mathfrak{p}$ (the statement is formulated with $\mathfrak{p}$ and the hypothesis that it is prime as final binders, so the conclusion is the membership $r \in \mathfrak{p}$ for that prime). Since the intersection of all prime ideals is the nilradical, the conclusion says equivalently that $r$ is nilpotent. Here $R$ is taken in the lowest universe.
--
--   This is a spreading-out statement on $\operatorname{Spec} R$ for a local ring: a pointwise quadratic relation $r(r^{2} - d) = 0$ together with the vanishing of $r$ at the closed point and at all points of residue characteristic zero forces $r$ to vanish at every point. It is used in the Čerednik–Drinfeld part of the development, in the computation of the trace attached to a fake elliptic curve ([`CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.trace_eq_of_tower_of_forall_isPullback_of_isCommutative_of_smoothOfRelativeDimension)), where such a relation is available prime by prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.mem_of_mul_sq_sub_intCast_mem_of_forall_charZero
    {R : Type} [CommRing R] [IsLocalRing R] (r : R) (d : ℤ)
    (hmax : r ∈ IsLocalRing.maximalIdeal R)
    (hquad : ∀ 𝔭 : Ideal R, 𝔭.IsPrime → r * (r ^ 2 - (d : R)) ∈ 𝔭)
    (hzero : ∀ 𝔭 : Ideal R, 𝔭.IsPrime → CharZero (R ⧸ 𝔭) → r ∈ 𝔭)
    (𝔭 : Ideal R) (h𝔭 : 𝔭.IsPrime) : r ∈ 𝔭 := by sorry
