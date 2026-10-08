-- Prove2me | Theorems.Thm_MazurCampaign_finite_group_classification
-- name    : MazurCampaign.finite_group_classification
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T07:18:07.530315+00:00
-- url     : https://prove2.me/theorems/49a71ed3-f32e-44d3-8653-feb86d5eebf7
-- title:
--   Finite-abelian reduction to the fifteen Mazur groups
-- statement:
--   Let $G$ be a finite abelian group, written additively. Suppose the order of every element belongs to $\{1,2,3,4,5,6,7,8,9,10,12\}$, and none of the following groups embeds in $G$: $(\mathbb Z/2\mathbb Z)^3$, $(\mathbb Z/3\mathbb Z)^2$, $(\mathbb Z/4\mathbb Z)^2$, $(\mathbb Z/5\mathbb Z)^2$, $(\mathbb Z/7\mathbb Z)^2$, $\mathbb Z/2\mathbb Z\times\mathbb Z/10\mathbb Z$, or $\mathbb Z/2\mathbb Z\times\mathbb Z/12\mathbb Z$. Then
--   $$G\cong\mathbb Z/n\mathbb Z\quad(n\in\{1,2,3,4,5,6,7,8,9,10,12\}),$$
--   or
--   $$G\cong\mathbb Z/2\mathbb Z\times\mathbb Z/(2m)\mathbb Z\quad(m\in\{1,2,3,4\}).$$
--   This is the finite-abelian step in Mazur's theorem. Finiteness, allowed element orders, and the seven subgroup exclusions are hypotheses here; the elliptic-curve campaign must establish each of them independently. The named downstream consumer is MazurCampaign.rationalTorsion_hasMazurClassification. The proof is adapted from the checked finite-group development in MazurTheorem.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/GroupTheory/FiniteClassification.lean#L251 ; https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/GroupTheory/FiniteClassification.lean#L363

import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.finite_group_classification
    {G : Type*} [AddCommGroup G] [Finite G]
    (horders : ∀ x : G, addOrderOf x ∈ MazurCampaign.cyclicOrders)
    (havoid : MazurTorsion.AvoidsMazurForbiddenSubgroups G) :
    (∃ n ∈ MazurCampaign.cyclicOrders, Nonempty (G ≃+ ZMod n)) ∨
      ∃ m ∈ MazurCampaign.bicyclicParameters,
        Nonempty (G ≃+ (ZMod 2 × ZMod (2 * m))) := by sorry
