-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_transport_eq_actRingEquiv
-- name    : NumberField.PlaceTransport.transport_eq_actRingEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c6ffdaf3-47dc-5048-a2a1-5113306b6eff
-- title:
--   Transport along σ agrees with the decomposition-group action on K_w
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and an $E$-algebra, and let $w$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$. Let $\sigma$ lie in [`NumberField.PlaceDecomp.decomp E K w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of the valuation subring of the $w$-adic valuation `w.valuation K` inside the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$, and assume $\sigma \cdot w = w$ for the natural action of automorphisms on height-one primes. The assertion is an equality of ring isomorphisms $w$-adic completion $\to$ $w$-adic completion, namely that [`NumberField.PlaceTransport.transport`](def/NumberField_PlaceTransport.html#L105) applied to $\sigma$ and to this witness of $\sigma \cdot w = w$ coincides with [`NumberField.PlaceDecomp.actRingEquiv`](def/NumberField_PlaceDecompositionAction.html#L105) applied to $\sigma$. Both sides are built as the same three-step composite: the identification `HeightOneSpectrum.adicCompletion.equiv K w` of `w.adicCompletion K` with the uniform-space completion of $K$ carrying the valuation `w.valuation K`, followed by the map induced on completions by $\sigma$ viewed as a ring isomorphism of $K$ transported along `WithVal.congr`, followed by the inverse of that identification; they differ only in how the uniform continuity of $\sigma$ and of $\sigma^{-1}$ for the $w$-adic topologies is obtained, from membership in the decomposition subgroup in one case and from the hypothesis $\sigma \cdot w = w$ in the other.
--
--   This identifies the transport isomorphism between adic completions, in the case where $\sigma$ fixes the place $w$, with the action of the decomposition group of $w$ on the local field $K_w$. It is the compatibility used when the Galois module of finite idèles is described place by place, and in particular when a product over an orbit $G \cdot w$ of local multiplicative groups is recognised as a coinduced module from the decomposition group; it is cited by the results on coinduced local unit groups and on idèle-theoretic Galois descent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_transport_eq_actRingEquiv.lean

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem NumberField.PlaceTransport.transport_eq_actRingEquiv (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (σ : NumberField.PlaceDecomp.decomp E K w)
    (h : (σ : K ≃ₐ[E] K) • w = w) :
    NumberField.PlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.PlaceDecomp.actRingEquiv σ := by sorry
