-- Prove2me | Theorems.Thm_MonoidHom_map_transfer_eq_transfer_comp
-- name    : MonoidHom.map_transfer_eq_transfer_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/a6890536-220b-52a7-a4e0-2c6d6635c93d
-- title:
--   Transfer is natural in the coefficient group
-- statement:
--   Let $G$ be a group and $H \le G$ a subgroup of finite index, let $A$ and $B$ be commutative groups, let $\varphi : H \to A$ be a homomorphism from $H$ (as a group in its own right) to $A$, let $f : A \to B$ be a homomorphism, and let $g \in G$. The assertion is the equality of elements of $B$
--   $$f\bigl(\operatorname{transfer}_{\varphi}(g)\bigr) \;=\; \operatorname{transfer}_{f \circ \varphi}(g),$$
--   where for a homomorphism $\psi$ from $H$ to a commutative group, $\operatorname{transfer}_{\psi} : G \to \cdot$ denotes Mathlib's `MonoidHom.transfer` of $\psi$, the Verlagerung attached to the finite-index subgroup $H$; on the right-hand side the coefficient homomorphism is the composite `f.comp ϕ`, that is $a \mapsto f(\varphi(a))$. In words: postcomposition with a homomorphism of commutative coefficient groups commutes with the formation of the transfer, so that $f \circ \operatorname{transfer}_{\varphi} = \operatorname{transfer}_{f \circ \varphi}$ as maps $G \to B$, evaluated here at an arbitrary $g$.
--
--   This is the naturality of the transfer (Verlagerung) in its coefficient group; in particular, for a character $\chi$ of $H$ with values in a commutative group, the transfer of $\chi$ factors as $\chi$ extended to $H^{\mathrm{ab}}$ composed with the transfer into $H^{\mathrm{ab}}$. It is used in the construction of explicit divisor-class and pullback identities for degree-zero Picard groups of curves, where transfer values of multiplicative automorphy factors must be transported along a homomorphism of coefficient groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_map_transfer_eq_transfer_comp.lean

import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MonoidHom.map_transfer_eq_transfer_comp
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) (g : G) :
    f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g := by sorry
