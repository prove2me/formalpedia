-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_card_over_mul_card_decomp_above
-- name    : NumberField.PlaceDecomp.card_over_mul_card_decomp_above
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/342ecc36-d7af-5724-9f14-be2c314ca810
-- title:
--   Places above v times decomposition group equals #Gal(K/E)
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra which is Galois over $E$, and let $v$ be a height one prime of the ring of integers $\mathcal{O}_E$. Write $w_0 =$ [`NumberField.PlaceAbove.above E K v`](def/NumberField_PlaceAbove.html#L27) for the height one prime of $\mathcal{O}_K$ chosen (by a choice function from an existence statement) among those lying above $v$, and let [`NumberField.PlaceDecomp.decomp E K w_0`](def/NumberField_PlaceDecompositionAction.html#L82) be the decomposition subgroup, inside the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$, of the valuation subring of $K$ attached to the $w_0$-adic valuation, i.e. the stabiliser of that valuation subring under the pointwise action of the automorphism group. The assertion is the identity of natural numbers
--   $$\#\{w : \text{height one prime of } \mathcal{O}_K \mid w.\mathrm{under}\,\mathcal{O}_E = v\}\cdot \#\,\mathrm{decomp}(E,K,w_0) = \#(K \simeq_{\mathrm{alg}[E]} K),$$
--   where the first factor is the cardinality of the subtype of those $w$ whose contraction to $\mathcal{O}_E$ is $v$, and all three cardinalities are taken in the sense of `Nat.card`.
--
--   This is the orbit–stabiliser relation for the action of $\mathrm{Gal}(K/E)$ on the finite places of $K$ above a fixed finite place $v$ of $E$: the number of such places times the order of the decomposition group of any one of them equals $[K:E]$. It is used downstream to exhibit the local degree at $v$ as the order of a decomposition group, in the computation of idele-theoretic fibre cardinalities and in an argument on automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_card_over_mul_card_decomp_above.lean

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem NumberField.PlaceDecomp.card_over_mul_card_decomp_above (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : HeightOneSpectrum (𝓞 E)) :
    Nat.card {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v} *
      Nat.card (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) = Nat.card (K ≃ₐ[E] K) := by sorry
