-- Prove2me | Theorems.Thm_MazurCampaign_allowed_point_orders
-- name    : MazurCampaign.allowed_point_orders
-- status  : Open
-- author  : @Vas
-- created : 2026-10-05T18:28:15.696384+00:00
-- url     : https://prove2.me/theorems/fc0381e4-7397-4546-b3fe-a89ed28e7890
-- title:
--   Corollary III.5.2: exact rational torsion point orders
-- statement:
--   For every elliptic curve $E/\mathbb Q$ and every rational point $P$ of finite additive order, the exact order of $P$ belongs to $\{1,2,3,4,5,6,7,8,9,10,12\}$. The identity has order one. Infinite-order points are excluded by the finite-order hypothesis.
-- source:
--   Barry Mazur, Modular curves and the Eisenstein ideal, Publications Mathématiques de l’IHÉS 47 (1977), pp. 33–186; Part III, §5, Theorem (5.1), its subsequent occurrence remark, and Corollary (5.2), printed p. 156 (PDF p. 125). https://doi.org/10.1007/BF02684339; https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf

import Definitions.Def_MazurCampaign_target_objects
open scoped WeierstrassCurve.Affine

theorem MazurCampaign.allowed_point_orders
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : IsOfFinAddOrder P) :
    addOrderOf P ∈ MazurCampaign.cyclicOrders := by sorry
