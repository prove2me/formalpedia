-- Prove2me | Theorems.Thm_IsArtinianRing_exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero
-- name    : IsArtinianRing.exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/abaeb984-35fd-508d-acf5-95fb269d4dae
-- title:
--   Nonzero socle element in an Artinian local ring
-- statement:
--   Let $B$ be a commutative ring (in the base universe) which is local in Mathlib's sense and Artinian as a ring, and suppose its maximal ideal $\mathfrak m = \mathrm{maximalIdeal}\,B$ is not the zero ideal, i.e. $B$ is not a field. The assertion is that there exists an element $t \in B$ with the three properties: $t \neq 0$; $t$ lies in $\mathfrak m$; and for every $m \in \mathfrak m$ one has $m \cdot t = 0$. In other words, the socle $\{t : \mathfrak m t = 0\}$ of $B$ meets $\mathfrak m \setminus \{0\}$: there is a nonzero element of the maximal ideal annihilated by the whole maximal ideal. Note that the annihilation is stated elementwise, as $m * t = 0$ for each $m \in \mathfrak m$, rather than as an equality of ideals, and that no finiteness of residue field or excellence assumption enters.
--
--   This is the standard existence of a nonzero socle element in an Artin local ring that is not a field; the ideal $(t)$ it produces is a one-dimensional kernel, so that $B \twoheadrightarrow B/(t)$ is a small extension. It is used in the deformation-theoretic argument for [`CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily), where such a filtration by small extensions allows an induction on the length of an Artin local test object, the base case being the dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsArtinianRing_exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsArtinianRing.exists_ne_zero_mem_maximalIdeal_forall_mul_eq_zero
    (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (h : IsLocalRing.maximalIdeal B ≠ ⊥) :
    ∃ t : B, t ≠ 0 ∧ t ∈ IsLocalRing.maximalIdeal B ∧ ∀ m ∈ IsLocalRing.maximalIdeal B, m * t = 0 := by sorry
