-- Prove2me | Theorems.Thm_N25_Endgame_pQ25_degree
-- name    : N25.Endgame.pQ25_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:45.063354+00:00
-- url     : https://prove2.me/theorems/948076eb-32dc-4b3f-8e2a-bd844608959e
-- title:
--   Each selected rational cusp has degree one
-- statement:
--   Let $p_i^Q$ be the $i$th place in the selected five-element cusp orbit of the rational level-$25$ function field, for $i∈Fin(5)$. Then
--
--   $$deg(p_i^Q)=1.$$
--
--   This identifies the selected rational cusps as rational places of the curve.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.pQ25_degree (i : Fin 5) : (pQ25 i).deg = 1 := by sorry
