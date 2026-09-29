-- Prove2me | Theorems.Thm_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv
-- name    : NumberField.InfinitePlaceTransport.transport_eq_actRingEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/3b61c3a4-7d15-571a-b003-dbf926901b67
-- title:
--   Transport along σ equals the decomposition-group action on K_w
-- statement:
--   Let $E$ and $K$ be fields with $K$ an $E$-algebra, and let $w$ be an infinite place of $K$ (no number-field hypothesis is imposed). Let $\sigma$ be an element of [`NumberField.InfPlaceDecomp.decomp E K w`](def/NumberField_ArchimedeanIdeleModule.html#L23), i.e. of the stabiliser of $w$ for the action of the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$ on the infinite places of $K$, and let $h$ witness that the underlying automorphism satisfies $\sigma \bullet w = w$. The assertion is an equality of ring isomorphisms $K_w \to K_w$ of the completion of $K$ at $w$: the isomorphism [`NumberField.InfinitePlaceTransport.transport`](def/NumberField_InfinitePlaceTransport.html#L32) attached to $\sigma$ and the witness $h$ — namely the identification of $w.\mathrm{Completion}$ with the uniform-space completion of `WithAbs w.1`, followed by `UniformSpace.Completion.mapRingEquiv` of the isometric ring equivalence `WithAbs.congr w.1 w.1 σ`, followed by the inverse identification — coincides with [`NumberField.InfPlaceDecomp.actRingEquiv σ`](def/NumberField_ArchimedeanIdeleModule.html#L36), the same three-step composite in which the continuity of the map and of its inverse are instead deduced from the membership of $\sigma$ and of $\sigma^{-1}$ in the stabiliser.
--
--   This is the compatibility statement identifying the transport isomorphism between archimedean completions, in the case where the automorphism fixes the place, with the action of the decomposition group $D_w$ on $K_w$ used to make $K_w^\times$ a $D_w$-module. It is invoked in the cohomological computations with archimedean idèles, where values of a coinduced cochain at $dg$ with $d \in D_w$ must be compared with its value at $g$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv.lean

import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.InfinitePlaceTransport.transport_eq_actRingEquiv (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (h : (σ : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.InfPlaceDecomp.actRingEquiv σ := by sorry
