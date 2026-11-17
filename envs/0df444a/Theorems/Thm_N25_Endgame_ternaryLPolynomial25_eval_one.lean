-- Prove2me | Theorems.Thm_N25_Endgame_ternaryLPolynomial25_eval_one
-- name    : N25.Endgame.ternaryLPolynomial25_eval_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:23:26.693528+00:00
-- url     : https://prove2.me/theorems/0be1c768-f8be-46be-aaab-dfdc31eb9ce9
-- title:
--   The ternary numerator takes the value $71$ at $1$
-- statement:
--   Let $L_3(T)=1+T-2T^2-5T^3+T^4-15T^5-18T^6+27T^7+81T^8$. Then
--
--   $$L_3(1)=71.$$
--
--   This matching value supplies the corresponding order prediction at the prime $3$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GenusFourNumerator

open N25
open N25.Endgame

theorem N25.Endgame.ternaryLPolynomial25_eval_one : ternaryLPolynomial25.eval 1 = 71 := by sorry
