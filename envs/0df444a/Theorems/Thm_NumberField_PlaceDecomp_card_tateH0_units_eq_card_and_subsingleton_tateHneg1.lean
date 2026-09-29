-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1
-- name    : NumberField.PlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8f617486-5d4d-5ba3-8a00-9b9947e476fa
-- title:
--   Tate cohomology of local units in cyclic degrees 0 and -1
-- statement:
--   Let $E$ and $K$ be fields with $K$ a number field and $K$ an $E$-algebra, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_K$. Write $G =$ [`NumberField.PlaceDecomp.decomp E K w`](def/NumberField_PlaceDecompositionAction.html#L82) for the decomposition subgroup of $E$-algebra automorphisms of $K$ attached to the valuation subring of the $w$-adic valuation of $K$, and assume $G$ is finite and cyclic. The multiplicative action of $G$ on the units $(K_w)^\times$ of the $w$-adic completion $K_w$ makes `Rep.ofMulDistribMulAction` a representation of $G$ on the additive group $\mathrm{Additive}\,(K_w)^\times$, and for such a representation $A$ the project defines `tateH0 A` as the invariants modulo the image of the norm map `normBar`, the factorisation of $x \mapsto \sum_{g \in G} g\cdot x$ through the coinvariants, and `tateHneg1 A` as the kernel of `normBar` on the coinvariants. The assertion is the conjunction: the cardinality of `tateH0` of this representation equals `Nat.card` of $G$, and `tateHneg1` of this representation is a subsingleton, i.e. vanishes.
--
--   This is the local norm-index computation for a cyclic local extension together with Hilbert's Theorem 90 in Tate degree $-1$: the fixed field $K_{w,0}$ of $G$ inside $K_w$ satisfies $[K_{w,0}^\times : N_{K_w/K_{w,0}}K_w^\times] = |G|$ and $\hat H^{-1}(G, K_w^\times) = 0$. It feeds the global computation of the Tate cohomology of the idele units at finite places, [`NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1`](thm.html#NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1), and is used downstream in the comparison of tensor constructions for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1 (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K))
    [Fintype (NumberField.PlaceDecomp.decomp E K w)] [IsCyclic (NumberField.PlaceDecomp.decomp E K w)] :
    Nat.card (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ).tateH0 =
      Nat.card (NumberField.PlaceDecomp.decomp E K w) ∧
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ).tateHneg1 := by sorry
