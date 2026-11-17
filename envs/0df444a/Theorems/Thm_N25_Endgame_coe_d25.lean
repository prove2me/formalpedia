-- Prove2me | Theorems.Thm_N25_Endgame_coe_d25
-- name    : N25.Endgame.coe_d25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:20.666074+00:00
-- url     : https://prove2.me/theorems/a9699be5-1a7b-40eb-b3fa-1e002e462486
-- title:
--   The distinguished rational class is the first cusp difference
-- statement:
--   Let $p_0,p_1$ be the first two selected geometric cusps and let $d$ be the distinguished element of the rational fixed subgroup of the level-$25$ Jacobian. Viewed in the ambient Jacobian, $d$ is exactly the degree-zero point-difference class
--
--   $$d=[p_0-p_1].$$
--
--   This unfolds the abstractly packaged cuspidal generator into the divisor class used in reduction calculations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CuspidalSubgroup
import Theorems.Thm_N25_Endgame_pG25_degree
import Definitions.Def_N25_SelectedCusps

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.coe_d25 :
    (d25 : N25.J) = pointDiff (pG25 0) (pG25 1) ((pG25_degree 0).trans (pG25_degree 1).symm) := by sorry
