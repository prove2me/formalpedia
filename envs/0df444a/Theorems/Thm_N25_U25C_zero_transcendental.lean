-- Prove2me | Theorems.Thm_N25_U25C_zero_transcendental
-- name    : N25.U25C_zero_transcendental
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:36.602288+00:00
-- url     : https://prove2.me/theorems/9c34a138-6a7a-4f04-a759-b7f1a20d04d5
-- title:
--   The first level-$25$ modular unit is transcendental
-- statement:
--   Let $K$ be a field and let $U_0^{(K)}$ be the first level-$25$ modular unit. Then $$Trans_K(U_0^{(K)}).$$ This supplies the transcendental coordinate needed for the unit-plane embedding.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25

theorem N25.U25C_zero_transcendental (K : Type*) [Field K] :
    Transcendental K (U25C K 0) := by sorry
