-- Prove2me | Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
-- name    : M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/d6c9cff9-0ee1-5220-99d9-eee0315a7b03
-- title:
--   Finite coordinates of the genuine Galois descent action
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\sigma$ be a $K$-algebra automorphism of $L$. Let $x$ be an element of the adèle ring $\mathbb{A}_L$ of $L$ (formed as the product of its archimedean part and the finite adèle ring of $\mathcal{O}_L$, so that $x.2$ is the finite part of $x$), and let $w, w'$ be height-one primes of $\mathcal{O}_L$ with $\sigma \cdot w = w'$, the hypothesis $h$ recording this equality. Write $\mathrm{act}$ for the monoid homomorphism from $\mathrm{Aut}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ belonging to the descent datum `genuineDescentDatum K L`, namely the one obtained by transporting $\mathrm{id} \otimes \sigma$ on $\mathbb{A}_K \otimes_K L$ through the algebra isomorphism `genuineTensorEquiv K L` from $\mathbb{A}_K \otimes_K L$ (with $\mathbb{A}_K$ acting through `genuineβ K L`) to $\mathbb{A}_L$, which sends $1 \otimes l$ to the image of $l$. The assertion is that the $w'$-coordinate of the finite part of $\mathrm{act}(\sigma)(x)$ equals [`NumberField.PlaceTransport.transport`](def/NumberField_PlaceTransport.html#L105) $\sigma$ $h$ applied to the $w$-coordinate of the finite part of $x$, where that transport is the ring isomorphism $L_w \to L_{w'}$ got by completing $\sigma$ with respect to the valuations of $w$ and $w'$.
--
--   This identifies the genuine Galois action on the adèles in finite coordinates: it permutes the places by $\sigma$ and acts on the completions by the continuous extension of $\sigma$. It is the coordinate formula used throughout the adelic automorphic-form computations that read off components at a finite place, for instance in the lemmas on Hecke operators at a place and its $\sigma$-translate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply.lean

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers L) L)
    {w w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)} (h : σ • w = w') :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2 w'
      = NumberField.PlaceTransport.transport σ h (x.2 w) := by sorry
