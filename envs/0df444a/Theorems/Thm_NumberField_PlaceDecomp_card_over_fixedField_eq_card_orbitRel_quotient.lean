-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient
-- name    : NumberField.PlaceDecomp.card_over_fixedField_eq_card_orbitRel_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/58d94e79-16f6-5660-bd89-a1eef554c079
-- title:
--   Places of K^H above S count H-orbits on coprodᵥ G/Dᵥ
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra such that $K/E$ is Galois, and write $G = K \simeq_{\mathrm{alg}[E]} K$ for its automorphism group. Let $S$ be a finite set of nonzero prime ideals of the ring of integers $\mathcal{O}_E$ (elements of the height-one spectrum of $\mathcal{O}_E$), and let $H$ be a subgroup of $G$. On the left-hand side stands the number of nonzero primes $u$ of the ring of integers of the intermediate field $\mathrm{fixedField}\,H$, the subfield of $K$ of elements fixed by every element of $H$, whose contraction $u \cap \mathcal{O}_E$ (the prime `u.under (𝓞 E)`) belongs to $S$. On the right-hand side, for each $v \in S$ let `above E K v` be the chosen prime of $\mathcal{O}_K$ lying over $v$, and let `decomp E K` of that prime be the decomposition subgroup of $G$ attached to the valuation subring of the associated valuation on $K$; the right-hand side is the number of orbits of $H$, acting by left translation, on the disjoint union over $v \in S$ of the coset spaces $G / \mathrm{decomp}(\mathrm{above}(v))$. The assertion is that these two cardinalities, both taken as `Nat.card`, are equal.
--
--   This is the classical count of the finite places of a subfield $K^H$ of $K$ lying above a finite set $S$ of places of the base field: the places of $K$ over $v$ form a single $G$-orbit with stabiliser the decomposition group $D_v$, and the places of $K^H$ over $v$ are the $H$-orbits among them, so the total is $\sum_{v \in S} \#(H \backslash G / D_v)$. It is used in the computation of ranks of $S$-unit groups and their Galois invariants, in [`NumberField.SUnits.finrank_invariants_repModP_sUnitsRep_tensor_add`](thm.html#NumberField.SUnits.finrank_invariants_repModP_sUnitsRep_tensor_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient.lean

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem NumberField.PlaceDecomp.card_over_fixedField_eq_card_orbitRel_quotient (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E))) (H : Subgroup (K ≃ₐ[E] K)) :
    Nat.card {u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) ∈ S} =
      Nat.card (MulAction.orbitRel.Quotient H
        (Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) := by sorry
