-- Prove2me | Theorems.Thm_NumberField_FiniteSIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1
-- name    : NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c48dbdff-cd3a-5d9f-b339-8bdbee1056d2
-- title:
--   Tate groups of the finite S-idèle module
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an algebra over $E$ such that $K/E$ is Galois with cyclic group $G = K \simeq_{\mathrm{alg}[E]} K$, and let $S$ be a finite set of height-one primes of $\mathcal O_E$. Assume that for every height-one prime $w$ of $\mathcal O_K$ whose contraction $w \cap \mathcal O_E$ does not lie in $S$, the ramification index of $w$ over that contraction equals $1$. Consider the $\mathbb Z[G]$-representation [`NumberField.FiniteSIdele.obj E K S`](def/NumberField_FiniteSIdeleModule.html#L51), namely the product representation, indexed by the disjoint union of $\{v \in S\}$ and $\{v \notin S\}$, whose factor at $v \in S$ is the coinduction along the inclusion $D_v =$ [`NumberField.FiniteSIdele.D E K v`](def/NumberField_FiniteSIdeleModule.html#L15) $\hookrightarrow G$ of `localUnits E K v`, and whose factor at $v \notin S$ is the coinduction of `localIntegerUnits E K v`; here $D_v$ is the decomposition subgroup, in $G$, of the valuation subring of the chosen prime `PlaceAbove.above E K v` of $\mathcal O_K$ above $v$, and the two local representations of $D_v$ are those given by the multiplicative action on $K_{w(v)}^\times$ and on $\mathcal O_{w(v)}^\times$. With $\hat H^0$ the quotient of the invariants by the image of the norm map $\mathrm{Coinv} \to \mathrm{Inv}$ and $\hat H^{-1}$ its kernel, the assertion is that the cardinality of $\hat H^{0}$ of this representation equals $\prod_{v \in S} |D_v|$, and that $\hat H^{-1}$ of it is a subsingleton.
--
--   This is the idèle-theoretic input to the Herbrand-quotient computation for a cyclic extension of number fields: the Tate cohomology of the finite $S$-idèles is concentrated in degree $0$, of order the product of the local degrees over $S$. It is used by [`M4aHerbrand.finSIdeleFibreBox_tateCard_eq_localDegreeProd`](thm.html#M4aHerbrand.finSIdeleFibreBox_tateCard_eq_localDegreeProd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_FiniteSIdele_card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_NumberField_FiniteSIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1 (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] [IsCyclic (K ≃ₐ[E] K)] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hSram : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    Nat.card (NumberField.FiniteSIdele.obj E K S).tateH0 = ∏ v ∈ S, Nat.card (NumberField.FiniteSIdele.D E K v) ∧
    Subsingleton (NumberField.FiniteSIdele.obj E K S).tateHneg1 := by sorry
