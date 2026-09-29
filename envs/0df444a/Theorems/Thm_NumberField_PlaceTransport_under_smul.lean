-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_under_smul
-- name    : NumberField.PlaceTransport.under_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/26648334-412e-50c3-91e1-ea7c34d6071e
-- title:
--   Conjugation by Aut(K/E) fixes the place below
-- statement:
--   Let $E$ and $K$ be fields with $K$ an $E$-algebra (no number-field or finiteness hypothesis is imposed beyond the instances needed for the notions involved), let $\sigma : K \simeq_{\mathrm{alg}[E]} K$ be an automorphism of $K$ as an $E$-algebra, and let $w$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_K =$ `NumberField.RingOfIntegers K`, i.e. a nonzero prime ideal of height one. Writing $\sigma \bullet w$ for the transported point given by the scoped action of $K \simeq_{\mathrm{alg}[E]} K$ on the height-one spectrum of $\mathcal{O}_K$ supplied by the `NumberField.PlaceTransport` development, and writing $v.\mathrm{under}\,\mathcal{O}_E$ for the height-one prime of $\mathcal{O}_E =$ `NumberField.RingOfIntegers E` whose underlying ideal is the contraction of the ideal of $v$ along the algebra map $\mathcal{O}_E \to \mathcal{O}_K$, the assertion is the equality $$(\sigma \bullet w).\mathrm{under}\,\mathcal{O}_E = w.\mathrm{under}\,\mathcal{O}_E$$ of points of the height-one spectrum of $\mathcal{O}_E$.
--
--   This is the statement that the restriction map on finite places commutes with conjugation by $\mathrm{Aut}(K/E)$: the fibre $\{w : w|_E = v\}$ over a fixed place $v$ of $E$ is stable under the automorphism group. It is what allows the automorphism group to act on place-indexed families over the primes above a fixed $v$, and is used in the coordinate descriptions of descent data and in the counting of idèle fibres over a place of the base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_under_smul.lean

import Mathlib
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem NumberField.PlaceTransport.under_smul (E K : Type*) [Field E] [Field K] [Algebra E K]
    (σ : K ≃ₐ[E] K) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (σ • w).under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E) := by sorry
