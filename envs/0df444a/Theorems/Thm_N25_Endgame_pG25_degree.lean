-- Prove2me | Theorems.Thm_N25_Endgame_pG25_degree
-- name    : N25.Endgame.pG25_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:30.401883+00:00
-- url     : https://prove2.me/theorems/7a3646ab-4f4d-4213-9a43-8f413e7dbc16
-- title:
--   Each selected geometric cusp has degree one
-- statement:
--   Let $p_i^G$ be the $i$th place in the selected five-element geometric cusp orbit, for $i∈Fin(5)$. Then
--
--   $$deg(p_i^G)=1.$$
--
--   This makes every selected geometric cusp eligible for degree-zero point-difference constructions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.pG25_degree (i : Fin 5) : (pG25 i).deg = 1 := by sorry
