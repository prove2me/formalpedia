-- Prove2me | Theorems.Thm_N25_gamma_pow_five
-- name    : N25.gamma_pow_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:04.419822+00:00
-- url     : https://prove2.me/theorems/89dcb295-96bc-4513-97ba-7ff401eafeb0
-- title:
--   The selected diamond operator has order dividing five
-- statement:
--   Let $J$ be the level-$25$ geometric Jacobian carrier and let $γ:J→J$ be the selected diamond operator. For every $x∈J$, five successive applications of $γ$ return $x$: $$γ^5(x)=x.$$ This supplies the order-five symmetry used to construct the endomorphisms in the descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.gamma_pow_five (x : N25.J) : N25.gamma (N25.gamma (N25.gamma (N25.gamma (N25.gamma x)))) = x := by sorry
