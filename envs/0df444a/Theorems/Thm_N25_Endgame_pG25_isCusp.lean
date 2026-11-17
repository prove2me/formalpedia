-- Prove2me | Theorems.Thm_N25_Endgame_pG25_isCusp
-- name    : N25.Endgame.pG25_isCusp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:22.140914+00:00
-- url     : https://prove2.me/theorems/956c259e-facd-4538-b6c3-059c660a351a
-- title:
--   Each selected geometric place is a cusp
-- statement:
--   Let $p_i^G$ be the $i$th selected geometric place, let $F_{\overline{ℚ}}$ be the geometric level-$25$ function field, and let $ι(j_{25})$ be the embedded modular $j$-function. Then
--
--   $$ι(j_{25})∉𝒪_{p_i^G}.$$
--
--   Thus every selected geometric place is a cusp, as required for the cuspidal divisor calculations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.pG25_isCusp (i : Fin 5) :
    ModularCurve.IsCusp (emb25 j25) (pG25 i) := by sorry
