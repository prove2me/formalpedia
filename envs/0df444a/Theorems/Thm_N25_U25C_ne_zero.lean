-- Prove2me | Theorems.Thm_N25_U25C_ne_zero
-- name    : N25.U25C_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:51.259551+00:00
-- url     : https://prove2.me/theorems/4a3b1ced-bb07-4d37-ae37-2143ac9d7c44
-- title:
--   Every level-$25$ modular unit is nonzero over every field
-- statement:
--   Let $K$ be a field and let $U_i^{(K)}$ be the $i$th of the five level-$25$ modular units. Then $$U_i^{(K)}≠0.$$ This licenses the unit ratios used as function-field coordinates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Units

set_option autoImplicit false
open N25

theorem N25.U25C_ne_zero (K : Type*) [Field K] (i : Fin 5) : U25C K i ≠ 0 := by sorry
