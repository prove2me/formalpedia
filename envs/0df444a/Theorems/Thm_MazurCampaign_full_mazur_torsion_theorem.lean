-- Prove2me | Theorems.Thm_MazurCampaign_full_mazur_torsion_theorem
-- name    : MazurCampaign.full_mazur_torsion_theorem
-- status  : Open
-- author  : @Vas
-- created : 2026-10-05T18:28:39.295664+00:00
-- url     : https://prove2.me/theorems/94a3c19d-4c9a-46cd-94d8-57d568f13288
-- title:
--   Full Mazur torsion theorem: finiteness, classification, and all fifteen occurrences
-- statement:
--   The rational torsion subgroup of every elliptic curve over $\mathbb Q$ is finite and isomorphic to one of the eleven cyclic groups $\mathbb Z/n\mathbb Z$ ($1\le n\le10$ or $n=12$) or four bicyclic groups $\mathbb Z/2\mathbb Z\times\mathbb Z/(2m)\mathbb Z$ ($1\le m\le4$). Conversely, every one of these fifteen groups is the full rational torsion subgroup of some elliptic curve over $\mathbb Q$. Thus the statement gives both necessity and occurrence, with explicit finiteness and no additional arithmetic hypotheses.
-- source:
--   Barry Mazur, Modular curves and the Eisenstein ideal, Publications Mathématiques de l’IHÉS 47 (1977), pp. 33–186; Part III, §5, Theorem (5.1), its subsequent occurrence remark, and Corollary (5.2), printed p. 156 (PDF p. 125). https://doi.org/10.1007/BF02684339; https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf

import Definitions.Def_MazurCampaign_target_objects
open scoped WeierstrassCurve.Affine

theorem MazurCampaign.full_mazur_torsion_theorem
    :
    (∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
      (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite ∧
        MazurCampaign.HasMazurClassification E) ∧
    (∀ n ∈ MazurCampaign.cyclicOrders,
      ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
        Nonempty (MazurCampaign.RationalTorsion E ≃+ ZMod n)) ∧
    (∀ m ∈ MazurCampaign.bicyclicParameters,
      ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
        Nonempty (MazurCampaign.RationalTorsion E ≃+ (ZMod 2 × ZMod (2 * m)))) := by sorry
