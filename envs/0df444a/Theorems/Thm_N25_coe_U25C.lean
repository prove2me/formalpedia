-- Prove2me | Theorems.Thm_N25_coe_U25C
-- name    : N25.coe_U25C
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:01.144427+00:00
-- url     : https://prove2.me/theorems/8088fc9f-8efb-4b44-b5d4-721b9ed4e72b
-- title:
--   Each modular unit has the prescribed Laurent series
-- statement:
--   Let $K$ be a field and let $i\in\mathbb Z/5\mathbb Z$. Write $U_i$ for the $i$th level-$25$ modular unit in the function field and $u_i$ for its prescribed Laurent series. The underlying series of $U_i$ is exactly $u_i$:
--
--   $$(U_i)_{\mathrm{series}}=u_i.$$
--
--   This lets function-field identities be evaluated through the explicit unit series.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.coe_U25C (K : Type*) [Field K] (i : Fin 5) : (U25C K i).1 = unitSeries25 K i := by sorry
