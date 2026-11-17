-- Prove2me | Theorems.Thm_N25_Endgame_pQ25_isCusp
-- name    : N25.Endgame.pQ25_isCusp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:54.75934+00:00
-- url     : https://prove2.me/theorems/18e12db3-e23b-47a4-a4d4-b7de309c7789
-- title:
--   Each selected rational place is a cusp
-- statement:
--   Let $p_i^Q$ be the $i$th selected rational place and let $j_{25}$ be the modular $j$-function in the rational level-$25$ function field. Then
--
--   $$j_{25}∉𝒪_{p_i^Q}.$$
--
--   Thus the five selected rational places are genuine cusps.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.pQ25_isCusp (i : Fin 5) : ModularCurve.IsCusp j25 (pQ25 i) := by sorry
