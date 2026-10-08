-- Prove2me | Theorems.Thm_MazurCampaign_rationalTorsion_hasMazurClassification
-- name    : MazurCampaign.rationalTorsion_hasMazurClassification
-- status  : Open
-- author  : @Vas
-- created : 2026-10-05T18:28:19.373932+00:00
-- url     : https://prove2.me/theorems/fb13bcaf-d53a-4423-ae06-4181807d8a1f
-- title:
--   Theorem III.5.1: unconditional rational torsion group classification
-- statement:
--   For every elliptic curve $E/\mathbb Q$, the entire torsion subgroup of $E(\mathbb Q)$ is isomorphic as an additive group to $\mathbb Z/n\mathbb Z$ for $n\in\{1,2,3,4,5,6,7,8,9,10,12\}$, or to $\mathbb Z/2\mathbb Z\times\mathbb Z/(2m)\mathbb Z$ for $m\in\{1,2,3,4\}$. No finiteness, rank, reduction, modularity, or supplied-classification hypothesis is assumed.
-- source:
--   Barry Mazur, Modular curves and the Eisenstein ideal, Publications Mathématiques de l’IHÉS 47 (1977), pp. 33–186; Part III, §5, Theorem (5.1), its subsequent occurrence remark, and Corollary (5.2), printed p. 156 (PDF p. 125). https://doi.org/10.1007/BF02684339; https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf

import Definitions.Def_MazurCampaign_target_objects
open scoped WeierstrassCurve.Affine

theorem MazurCampaign.rationalTorsion_hasMazurClassification
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurCampaign.HasMazurClassification E := by sorry
