-- Prove2me | Theorems.Thm_NumberField_InfinitePlaceTransport_transport_trans_transport
-- name    : NumberField.InfinitePlaceTransport.transport_trans_transport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/4d1bb46b-fd14-5fdb-81db-e48c5dfa07ff
-- title:
--   Transport of completions is compatible with composition
-- statement:
--   Let $E$ and $K$ be fields with $K$ an $E$-algebra, let $\sigma,\tau$ be $E$-algebra automorphisms of $K$, and let $w,w',w''$ be infinite places of $K$. Assume three separate witnesses: $h_1 : \tau\cdot w = w'$, $h_2 : \sigma\cdot w' = w''$ and $h_3 : (\sigma\tau)\cdot w = w''$, for the action of $K\simeq_{\mathrm{alg}[E]}K$ on infinite places. For such data, [`NumberField.InfinitePlaceTransport.transport`](def/NumberField_InfinitePlaceTransport.html#L32) produces a ring isomorphism between the completions at the two places: it is the identification of $w$'s completion with the completion of $K$ for the absolute value attached to $w$ (`InfinitePlace.Completion.equiv`), followed by the completion of the ring isomorphism of $K$ given by $\sigma$, read as a map from $K$ with the $w$-absolute value to $K$ with the $w'$-absolute value — uniformly continuous in both directions precisely because $\sigma\cdot w=w'$ — followed by the inverse identification at the target place. The assertion is that the composite of `transport τ h₁ : w.Completion ≃+* w'.Completion` with `transport σ h₂ : w'.Completion ≃+* w''.Completion`, formed using `RingEquiv.trans`, equals `transport (σ * τ) h₃ : w.Completion ≃+* w''.Completion`.
--
--   This is the cocycle (composition) law for transporting completions along Galois-conjugate infinite places; keeping the three equalities of places as independent hypotheses makes the statement applicable without rewriting indices. Together with the corresponding normalisation at the identity it is what turns "shift the index, then transport" into a genuine group action on families of completions indexed by the places above a fixed archimedean place, and it is used in the treatment of archimedean ideles and the associated coinduced modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlaceTransport_transport_trans_transport.lean

import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.InfinitePlaceTransport.transport_trans_transport (E K : Type*) [Field E] [Field K] [Algebra E K]
    (σ τ : K ≃ₐ[E] K) {w w' w'' : NumberField.InfinitePlace K}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') :
    (NumberField.InfinitePlaceTransport.transport τ h₁).trans (NumberField.InfinitePlaceTransport.transport σ h₂)
      = NumberField.InfinitePlaceTransport.transport (σ * τ) h₃ := by sorry
