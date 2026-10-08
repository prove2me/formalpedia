-- Prove2me | Theorems.Thm_MazurCampaign_rational_torsion_finite
-- name    : MazurCampaign.rational_torsion_finite
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-05T18:28:10.485119+00:00
-- url     : https://prove2.me/theorems/0959ed63-c84f-4737-963f-b8a0ddfc7f2b
-- title:
--   Finiteness of rational torsion
-- statement:
--   For every elliptic curve $E/\mathbb Q$, its entire rational torsion subgroup is finite. Ellipticity is the sole curve hypothesis.
-- source:
--   Barry Mazur, Modular curves and the Eisenstein ideal, Publications Mathématiques de l’IHÉS 47 (1977), pp. 33–186; Part III, §5, Theorem (5.1), its subsequent occurrence remark, and Corollary (5.2), printed p. 156 (PDF p. 125). https://doi.org/10.1007/BF02684339; https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf

import Definitions.Def_MazurCampaign_target_objects
open scoped WeierstrassCurve.Affine

theorem MazurCampaign.rational_torsion_finite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite := by sorry
