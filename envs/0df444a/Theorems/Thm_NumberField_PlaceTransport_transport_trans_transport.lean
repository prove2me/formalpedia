-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_transport_trans_transport
-- name    : NumberField.PlaceTransport.transport_trans_transport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/7902a61f-898f-5fd8-89e1-a72cf898345e
-- title:
--   Composition law for transport of adic completions along conjugation
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and an $E$-algebra, let $\sigma,\tau$ be $E$-algebra automorphisms of $K$, and let $w,w',w''$ be height-one primes of the ring of integers $\mathcal{O}_K$, i.e. points of `IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`. Assume three witnesses for the action of automorphisms on primes: $h_1 : \tau \cdot w = w'$, $h_2 : \sigma \cdot w' = w''$ and $h_3 : (\sigma\tau) \cdot w = w''$. For each such witness, [`NumberField.PlaceTransport.transport`](def/NumberField_PlaceTransport.html#L105) produces a ring isomorphism between the corresponding adic completions: it is the composite of the identification of $K_w$ with the uniform-space completion of $K$ equipped with the valuation of $w$, the completion of the ring isomorphism `WithVal.congr` induced by the underlying ring isomorphism of the automorphism (uniformly continuous in both directions because the automorphism carries the one valuation to the other), and the inverse of the corresponding identification at the target prime. The conclusion is that the transport attached to $\tau$ and $h_1$, from $K_w$ to $K_{w'}$, followed by the transport attached to $\sigma$ and $h_2$, from $K_{w'}$ to $K_{w''}$, equals the transport attached to the product $\sigma\tau$ and $h_3$, as ring isomorphisms $K_w \xrightarrow{\sim} K_{w''}$. The three hypotheses are independent binders, so no coercions along equalities of primes occur.
--
--   This is the cocycle (functoriality) law making the family of completions $(K_w)_w$ an equivariant family over the set of finite places of $K$ viewed as a set with an action of the $E$-automorphism group, the identity automorphism giving the unit law. It is used throughout the treatment of Galois actions on place-indexed idèlic modules and on local unit groups, and is cited, among others, by results on finite $S$-idèles and on coordinate descriptions of descent data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_transport_trans_transport.lean

import Mathlib
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem NumberField.PlaceTransport.transport_trans_transport (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (σ τ : K ≃ₐ[E] K) {w w' w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') :
    (NumberField.PlaceTransport.transport τ h₁).trans (NumberField.PlaceTransport.transport σ h₂)
      = NumberField.PlaceTransport.transport (σ * τ) h₃ := by sorry
