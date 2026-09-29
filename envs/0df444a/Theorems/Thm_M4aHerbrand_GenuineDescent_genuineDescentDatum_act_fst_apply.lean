-- Prove2me | Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
-- name    : M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/1050f9a0-64b8-5c35-94bc-cfa022d20002
-- title:
--   Infinite coordinates of the genuine Galois descent action
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, let $x$ be an element of the adèle ring `NumberField.AdeleRing (𝓞 L) L` (so that $x.1$ is its infinite part, a function assigning to each infinite place $u$ of $L$ an element of the completion $L_u$), and let $w,w'$ be infinite places of $L$ with $\sigma \bullet w = w'$, witnessed by $h$. The datum [`M4aHerbrand.GenuineDescent.genuineDescentDatum K L`](def/M4aHerbrand_GenuineDescent.html#L92) is the `IdeleGaloisDescent` structure for $\mathcal O_L$, $K$, $L$ — a monoid homomorphism `act` from $\mathrm{Aut}(L/K)$ to the ring automorphisms of $\mathbb A_L$, together with compatibility with `algebraMap` from $L$ and continuity — obtained by transporting the automorphism $\mathrm{id} \otimes \sigma$ of $\mathbb A_K \otimes_K L$ along the $\mathbb A_K$-algebra isomorphism `genuineTensorEquiv K L` between $\mathbb A_K \otimes_K L$ and $\mathbb A_L$ (the $\mathbb A_K$-algebra structure coming from `genuineβ K L`). The assertion is that the $w'$-coordinate of the infinite part of `act σ x` equals [`NumberField.InfinitePlaceTransport.transport σ h`](def/NumberField_InfinitePlaceTransport.html#L32) applied to the $w$-coordinate of the infinite part of $x$, where `transport σ h` is the ring isomorphism $L_w \to L_{w'}$ obtained by completing the map on absolute-value-twisted copies of $L$ induced by $\sigma$.
--
--   This is the archimedean per-place description of the Galois action on adèles: the Galois group permutes the archimedean factors of $\mathbb A_L$ according to its action on infinite places, via the canonical isomorphisms $L_w \cong L_{\sigma w}$. It is the coordinatewise formula used by consumers that need the fibre automorphisms of the archimedean factors, for instance in the computation of adelic heights and of Hecke operators at infinity for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply.lean

import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers L) L)
    {w w' : NumberField.InfinitePlace L} (h : σ • w = w') :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 w'
      = NumberField.InfinitePlaceTransport.transport σ h (x.1 w) := by sorry
