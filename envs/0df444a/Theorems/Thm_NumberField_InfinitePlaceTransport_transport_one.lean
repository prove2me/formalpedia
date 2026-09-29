-- Prove2me | Theorems.Thm_NumberField_InfinitePlaceTransport_transport_one
-- name    : NumberField.InfinitePlaceTransport.transport_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/1e21b414-f55c-521d-9630-97f0db42dadb
-- title:
--   Transport along the identity automorphism is the identity
-- statement:
--   Let $E$ and $K$ be fields with $K$ an $E$-algebra, and let $w$ be an infinite place of $K$. Let $h$ be a proof that the identity element of the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$ fixes $w$ under the action of that group on infinite places, i.e. $1 \cdot w = w$. The transport isomorphism $\mathtt{transport}\ 1\ h$ attached to this datum — namely the composite of the identification `InfinitePlace.Completion.equiv w` of the completion $K_w$ with the uniform-space completion of $K$ equipped with the absolute value $w$, followed by the ring isomorphism of completions induced by `WithAbs.congr` applied to the underlying ring equivalence of the identity automorphism (the relevant maps being continuous because $1 \cdot w = w$ and because the inverse relation holds too), followed by the inverse of the identification for the target place — is asserted to be equal, as a ring isomorphism $K_w \simeq_{+*} K_w$, to the identity ring isomorphism `RingEquiv.refl w.Completion`.
--
--   This is the normalisation (unit) law for the transport of archimedean completions along $E$-automorphisms of $K$; together with the corresponding composition law it makes $\sigma \mapsto \mathtt{transport}\ \sigma$ behave as a cocycle of ring isomorphisms over the Galois action on infinite places. It is used in the treatment of archimedean ideles and local units, for instance in the identification of coinduced local unit groups and in the idelic cohomology computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlaceTransport_transport_one.lean

import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.InfinitePlaceTransport.transport_one (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl w.Completion := by sorry
