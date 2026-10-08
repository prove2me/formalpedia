-- Prove2me | Theorems.Thm_MazurCampaign_every_bicyclic_group_occurs
-- name    : MazurCampaign.every_bicyclic_group_occurs
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-05T18:28:27.791444+00:00
-- url     : https://prove2.me/theorems/d5306486-b5a4-4e86-8202-27fb52afe2fd
-- title:
--   Remark after III.5.1: occurrence of all four bicyclic groups
-- statement:
--   For each $m\in\{1,2,3,4\}$, there exists a nonsingular rational Weierstrass curve whose full rational torsion subgroup is isomorphic to $\mathbb Z/2\mathbb Z\times\mathbb Z/(2m)\mathbb Z$. The curve may depend on $m$.
-- source:
--   Barry Mazur, Modular curves and the Eisenstein ideal, Publications Mathématiques de l’IHÉS 47 (1977), pp. 33–186; Part III, §5, Theorem (5.1), its subsequent occurrence remark, and Corollary (5.2), printed p. 156 (PDF p. 125). https://doi.org/10.1007/BF02684339; https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf

import Definitions.Def_MazurCampaign_target_objects
open scoped WeierstrassCurve.Affine

theorem MazurCampaign.every_bicyclic_group_occurs
    (m : ℕ) (hm : m ∈ MazurCampaign.bicyclicParameters) :
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      Nonempty (MazurCampaign.RationalTorsion E ≃+ (ZMod 2 × ZMod (2 * m))) := by sorry
