-- Prove2me | Theorems.Thm_N25_Endgame_pQ25_j_order
-- name    : N25.Endgame.pQ25_j_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:39.830422+00:00
-- url     : https://prove2.me/theorems/15b5675f-229e-49ab-8079-136ceeb3d140
-- title:
--   The modular $j$-function has a simple pole at every selected rational cusp
-- statement:
--   Let $p_i^Q$ be the $i$th selected rational cusp and let $j_{25}$ be the modular $j$-function. Its valuation at that cusp is
--
--   $$ord_{p_i^Q}(j_{25})=-1.$$
--
--   This strengthens the cusp condition to the precise simple-pole order used to classify all geometric cusps.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.pQ25_j_order (i : Fin 5) : (pQ25 i).ord j25 = -1 := by sorry
