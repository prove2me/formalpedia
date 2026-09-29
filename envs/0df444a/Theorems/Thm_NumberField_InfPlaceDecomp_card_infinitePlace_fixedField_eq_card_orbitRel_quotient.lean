-- Prove2me | Theorems.Thm_NumberField_InfPlaceDecomp_card_infinitePlace_fixedField_eq_card_orbitRel_quotient
-- name    : NumberField.InfPlaceDecomp.card_infinitePlace_fixedField_eq_card_orbitRel_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/b39a5b84-f5e6-534a-b222-43d997920b89
-- title:
--   Infinite places of K^H count H-orbits on coprodᵥ G/Dᵥ
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra, and assume $K/E$ is Galois; write $G = K \simeq_{\mathrm{alg}[E]} K$ for its automorphism group, and let $H$ be a subgroup of $G$. On the one side stands the number of infinite places of the fixed field $\mathrm{IntermediateField.fixedField}\ H \subseteq K$, i.e. the subfield of elements fixed by every element of $H$. On the other side, for each infinite place $v$ of $E$ let $\mathrm{NumberField.ArchIdele.above}\ E\ K\ v$ be the infinite place of $K$ chosen (by a choice from an existence statement) above $v$, and let $\mathrm{NumberField.InfPlaceDecomp.decomp}$ applied to it be its stabiliser $D_v \le G$ for the action of $G$ on infinite places of $K$; form the disjoint union $\coprod_{v} G/D_v$ over the infinite places $v$ of $E$, on which $H$ acts by left translation in each fibre, and take the quotient by the orbit relation. The theorem asserts the equality of the two natural-number cardinalities: $\#\{\text{infinite places of } K^H\} = \#\bigl(H \backslash \coprod_{v \mid \infty} G/D_v\bigr)$.
--
--   This is the archimedean orbit count for a subextension of a Galois extension of number fields: the infinite places of $K^H$ are the $H$-orbits of infinite places of $K$, and the infinite places of $K$ are parametrised, place of $E$ by place of $E$, by the coset spaces $G/D_v$. It feeds the computation of ranks of $S$-unit groups and their invariants, being cited in the determination of the rank of the invariants of an $S$-unit representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfPlaceDecomp_card_infinitePlace_fixedField_eq_card_orbitRel_quotient.lean

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem NumberField.InfPlaceDecomp.card_infinitePlace_fixedField_eq_card_orbitRel_quotient (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (H : Subgroup (K ≃ₐ[E] K)) :
    Nat.card (InfinitePlace (IntermediateField.fixedField H)) =
      Nat.card (MulAction.orbitRel.Quotient H
        (Σ v : InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v))) := by sorry
