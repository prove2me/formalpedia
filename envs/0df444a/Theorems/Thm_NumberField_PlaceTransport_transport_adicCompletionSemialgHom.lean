-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_transport_adicCompletionSemialgHom
-- name    : NumberField.PlaceTransport.transport_adicCompletionSemialgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/9063b5ad-d561-5ce3-b171-2ea0eeafbc6f
-- title:
--   Place transport commutes with the canonical embeddings Eᵥ → K_w
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra, let $\sigma$ be an automorphism of $K$ as an $E$-algebra, and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_E$. Let $W$ and $W'$ be two extensions of $v$ to $\mathcal{O}_K$, that is, height-one primes $W.1, W'.1$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_E$ is $v$, and assume $h$ asserts that the natural action of $\sigma$ carries $W.1$ to $W'.1$. Then for every $y$ in the $v$-adic completion $E_v$ of $E$ one has $$\mathrm{transport}\,\sigma\,h\big(\iota_{W}(y)\big) = \iota_{W'}(y),$$ where $\iota_{W} : E_v \to K_{W.1}$ is `adicCompletionSemialgHom`, the semialgebra map over $\mathrm{algebraMap}\ E\ K$ obtained by completing the continuous inclusion of valued fields, and $\mathrm{transport}\,\sigma\,h : K_{W.1} \xrightarrow{\ \sim\ } K_{W'.1}$ is the ring isomorphism of completions induced, via the identifications of each $\mathfrak{p}$-adic completion with the uniform-space completion of $K$ equipped with the corresponding valuation, by $\sigma$ regarded as an isomorphism of valued fields from $(K, W.1\text{-valuation})$ to $(K, W'.1\text{-valuation})$.
--
--   This records that the family of canonical embeddings of $E_v$ into the completions of $K$ at the places above $v$ is equivariant for the Galois action: moving the place by $\sigma$ and then transporting does not change the image of $E_v$. It is the local ingredient in the coordinate description of the Galois descent datum on the finite adèles, and is cited in the construction of that datum and in the Herbrand-type index computations, as well as in a statement on simultaneous diagonalisation of automorphisms of products of adic completions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_transport_adicCompletionSemialgHom.lean

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem NumberField.PlaceTransport.transport_adicCompletionSemialgHom (E K : Type*) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] (σ : K ≃ₐ[E] K)
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)}
    (W W' : v.Extension (NumberField.RingOfIntegers K)) (h : σ • W.1 = W'.1) (y : v.adicCompletion E) :
    NumberField.PlaceTransport.transport σ h (W.adicCompletionSemialgHom E K y) = W'.adicCompletionSemialgHom E K y := by sorry
