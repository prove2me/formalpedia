-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_transport_one
-- name    : NumberField.PlaceTransport.transport_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/690a6eb9-cba2-5aad-8785-473db19ab60d
-- title:
--   Transport along the identity automorphism is the identity
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and $K$ an $E$-algebra, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$, i.e. a point of `IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`. Suppose $h$ witnesses that the identity element of the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$ fixes $w$ for the action of that group on the height-one spectrum, i.e. $1 \cdot w = w$. The assertion is that the transported ring isomorphism $\mathrm{transport}(1, h)$ of the $w$-adic completion $K_w$ is the identity. Here $\mathrm{transport}(\sigma, h)$, for $\sigma$ an $E$-automorphism with $\sigma \cdot w = w'$, is the ring isomorphism $K_w \simeq K_{w'}$ obtained by composing the canonical identification of `w.adicCompletion K` with the completion of $K$ for the valuation attached to $w$, the map on completions induced by $\sigma$ viewed as a ring isomorphism between the two valued copies of $K$ (uniformly continuous in both directions because $\sigma$ carries $w$ to $w'$), and the inverse of the corresponding identification at $w'$. Thus for $\sigma = 1$ and $w' = w$ this composite is equal, as a ring isomorphism of `w.adicCompletion K`, to `RingEquiv.refl`.
--
--   This records the unit law for the action of $\mathrm{Aut}(K/E)$ on the family of completions $w \mapsto K_w$ of a number field at its finite places; together with the corresponding composition law it makes that family equivariant. It is used in the cohomological analysis of idèles and of local integral units, for instance in the Herbrand-quotient computations and in the description of local coordinates on idèle groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_transport_one.lean

import Mathlib
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem NumberField.PlaceTransport.transport_one (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.PlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl (w.adicCompletion K) := by sorry
