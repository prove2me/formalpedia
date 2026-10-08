-- Prove2me | Theorems.Thm_MazurCampaign_every_cyclic_group_occurs
-- name    : MazurCampaign.every_cyclic_group_occurs
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-05T18:28:32.131633+00:00
-- url     : https://prove2.me/theorems/e27bf64b-c5f2-408f-b869-bc98d9d0c0a6
-- title:
--   Remark after III.5.1: occurrence of all eleven cyclic groups
-- statement:
--   For each $n\in\{1,2,3,4,5,6,7,8,9,10,12\}$, there exists a nonsingular rational Weierstrass curve whose full rational torsion subgroup is isomorphic to $\mathbb Z/n\mathbb Z$. The conclusion identifies the entire subgroup, rather than only exhibiting a point of order $n$.
-- source:
--   Barry Mazur, Modular curves and the Eisenstein ideal, Publications Mathématiques de l’IHÉS 47 (1977), pp. 33–186; Part III, §5, Theorem (5.1), its subsequent occurrence remark, and Corollary (5.2), printed p. 156 (PDF p. 125). https://doi.org/10.1007/BF02684339; https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf

import Definitions.Def_MazurCampaign_target_objects
open scoped WeierstrassCurve.Affine

theorem MazurCampaign.every_cyclic_group_occurs
    (n : ℕ) (hn : n ∈ MazurCampaign.cyclicOrders) :
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      Nonempty (MazurCampaign.RationalTorsion E ≃+ ZMod n) := by sorry
