-- Prove2me | Theorems.Thm_MulAction_ncard_orbit_inter_orbit_mul_card
-- name    : MulAction.ncard_orbit_inter_orbit_mul_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/ca5215d9-a72f-560e-b575-cefc97f9c5f1
-- title:
--   Orbit intersection count for a factorised transitive group action
-- statement:
--   Let $G$ be a finite group acting on a type $X$, the action being pretransitive (any two points of $X$ are in the same $G$-orbit), and let $H_1, H_2 \le G$ be subgroups satisfying the hypothesis `hprod`: every $g \in G$ can be written $g = h_1 h_2$ with $h_1 \in H_1$ and $h_2 \in H_2$. Then for all points $x_1, x_2 \in X$,
--   $$\#\bigl(H_1 x_1 \cap H_2 x_2\bigr) \cdot \#X = \#(H_1 x_1) \cdot \#(H_2 x_2),$$
--   where $H_i x_i$ denotes the orbit of $x_i$ under the restricted action of the subgroup $H_i$, the orbits and their intersection are counted with `Set.ncard` and $X$ with `Nat.card` (finiteness of $X$ follows from the finiteness of $G$ together with transitivity, so no separate hypothesis is imposed). Equivalently, the two orbits meet in exactly $\#(H_1x_1)\,\#(H_2x_2)/\#X$ points; note that the hypothesis is the factorisation $H_1 H_2 = G$ stated element-wise, which is strictly stronger than $H_1 \sqcup H_2 = \top$.
--
--   This is an orbit-counting identity: for a transitive action of a finite group factorised as $G = H_1H_2$, the orbits of the two subgroups intersect "independently", in the sense that the size of the intersection is the product of the orbit sizes divided by the size of $X$. It is used in the Galois-theoretic description of places of curves, where primes above a fixed prime correspond to orbits of the Galois group, to prove the identity [`AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber`](thm.html#AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber) relating ramification and residue-degree data along a fibre product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MulAction_ncard_orbit_inter_orbit_mul_card.lean

import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MulAction.ncard_orbit_inter_orbit_mul_card {G : Type*} [Group G] {X : Type*} [MulAction G X] [Finite G] [MulAction.IsPretransitive G X] (H₁ H₂ : Subgroup G) (hprod : ∀ g : G, ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂) (x₁ x₂ : X) : (MulAction.orbit H₁ x₁ ∩ MulAction.orbit H₂ x₂).ncard * Nat.card X = (MulAction.orbit H₁ x₁).ncard * (MulAction.orbit H₂ x₂).ncard := by sorry
