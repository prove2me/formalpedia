-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
-- name    : NumberField.PlaceTransport.stabilizer_eq_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/4fdcbbb3-53cc-5270-8955-0537e92d66cc
-- title:
--   Stabiliser of a finite place equals its decomposition subgroup
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and $K$ an $E$-algebra, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$, i.e. an element of `IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`. The group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$ acts on such primes by the place-transport action of the project (whose scoped notation is opened here). The assertion is an equality of subgroups of $K \simeq_{\mathrm{alg}[E]} K$: the stabiliser `MulAction.stabilizer (K ≃ₐ[E] K) w` of $w$ for that action coincides with [`NumberField.PlaceDecomp.decomp E K w`](def/NumberField_PlaceDecompositionAction.html#L82), which by definition is the decomposition subgroup, inside the $E$-automorphisms of $K$, of the valuation subring of $K$ attached to the $w$-adic valuation `w.valuation K` — that is, the subgroup of those $\sigma$ whose pointwise image of the valuation ring $\mathcal{O}_{K,w} \subseteq K$ is again $\mathcal{O}_{K,w}$. No finiteness, normality or algebraicity hypothesis on $K$ over $E$ is imposed.
--
--   This is the identification of the two standard descriptions of the decomposition group at a finite place: the stabiliser of the prime ideal, as in the inertia–decomposition theory for $\mathcal{O}_K$, and the stabiliser of the associated valuation subring of $K$. It lets results stated for one vocabulary be transferred to the other, and is used throughout the local–global and Herbrand-quotient parts of the development, for instance in the comparison of inertia subgroups and in the computations with local fundamental classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_stabilizer_eq_decomp.lean

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem NumberField.PlaceTransport.stabilizer_eq_decomp (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.stabilizer (K ≃ₐ[E] K) w = NumberField.PlaceDecomp.decomp E K w := by sorry
