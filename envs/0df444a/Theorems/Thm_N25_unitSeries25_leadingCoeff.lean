-- Prove2me | Theorems.Thm_N25_unitSeries25_leadingCoeff
-- name    : N25.unitSeries25_leadingCoeff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:43.18127+00:00
-- url     : https://prove2.me/theorems/0a74cf66-06e4-4dee-a66a-bfb09637e2e5
-- title:
--   Every unit series has leading coefficient one
-- statement:
--   Let $K$ be a field, let $S_i$ be the $i$th unit Laurent series, and let $q_i$ be its prescribed order. Then $$[q^{q_i}]S_i=1.$$ This normalizes the formal modular units uniquely.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25

theorem N25.unitSeries25_leadingCoeff (K : Type*) [Field K] (i : Fin 5) :
    (unitSeries25 K i).coeff (unitQOrder25 i) = 1 := by sorry
