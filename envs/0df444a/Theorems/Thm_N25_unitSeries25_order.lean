-- Prove2me | Theorems.Thm_N25_unitSeries25_order
-- name    : N25.unitSeries25_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:44.456195+00:00
-- url     : https://prove2.me/theorems/778dfeea-0527-45a3-84cf-a9b1a56480d1
-- title:
--   The order of each unit series is the prescribed integer
-- statement:
--   Let $K$ be a field, let $S_i$ be the $i$th level-$25$ unit Laurent series, and let $q_i$ be its tabulated q-order. Then $$\operatorname{ord}(S_i)=q_i.$$ This connects the formal series with the cusp-order calculations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25

theorem N25.unitSeries25_order (K : Type*) [Field K] (i : Fin 5) :
    (unitSeries25 K i).order = unitQOrder25 i := by sorry
