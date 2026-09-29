-- Prove2me | Theorems.Thm_NumberField_InfinitePlaceTransport_transport_algebraMap_completion
-- name    : NumberField.InfinitePlaceTransport.transport_algebraMap_completion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c27d1007-6f50-5436-b6dd-cc974537ace7
-- title:
--   Transport of archimedean completions commutes with base change
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $\sigma : L \simeq_{\text{alg}[K]} L$ be a $K$-algebra automorphism of $L$, let $v$ be an infinite place of $K$ and let $w, w'$ be infinite places of $L$ whose underlying absolute values lie over the absolute value of $v$, so that the structure maps $K_v \to L_w$ and $K_v \to L_{w'}$ of completions are available as `algebraMap`s. Assume $\sigma \bullet w = w'$ for the natural action of automorphisms on infinite places, and let $y \in K_v$ be arbitrary. Write $\mathrm{transport}\ \sigma\ h : L_w \simeq_{+*} L_{w'}$ for the ring isomorphism of completions obtained by identifying $L_w$ with the completion of $L$ equipped with the absolute value of $w$, applying the completion of the map induced on these normed copies of $L$ by $\sigma$ viewed as a ring isomorphism $L \simeq_{+*} L$ — continuous in both directions because $\sigma \bullet w = w'$ and, equivalently, $\sigma^{-1} \bullet w' = w$ — and then identifying back with $L_{w'}$. The theorem asserts that this isomorphism carries the image of $y$ under $K_v \to L_w$ to the image of $y$ under $K_v \to L_{w'}$.
--
--   This is the archimedean local compatibility saying that transport along $\sigma$ between the completions at conjugate places is a $K_v$-algebra map, i.e. the triangle formed by the two base-change maps $K_v \to L_w$, $K_v \to L_{w'}$ and $\mathrm{transport}\ \sigma$ commutes. It is used in the construction of the Galois descent datum on the adèle ring, where the infinite coordinates above $v$ are permuted by the transport maps while the $v$-coordinate is untouched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlaceTransport_transport_algebraMap_completion.lean

import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.LiesOver

theorem NumberField.InfinitePlaceTransport.transport_algebraMap_completion (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : NumberField.InfinitePlace K) {w w' : NumberField.InfinitePlace L}
    [w.1.LiesOver v.1] [w'.1.LiesOver v.1] (h : σ • w = w') (y : v.Completion) :
    NumberField.InfinitePlaceTransport.transport σ h (algebraMap v.Completion w.Completion y)
      = algebraMap v.Completion w'.Completion y := by sorry
