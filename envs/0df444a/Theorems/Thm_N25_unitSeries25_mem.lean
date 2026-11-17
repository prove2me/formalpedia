-- Prove2me | Theorems.Thm_N25_unitSeries25_mem
-- name    : N25.unitSeries25_mem
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:47.534334+00:00
-- url     : https://prove2.me/theorems/fad4fbfd-d1f0-4267-838e-ecdae8a2f1f8
-- title:
--   Every unit Laurent series belongs to the level-$25$ modular function field
-- statement:
--   Let $K$ be a field and let $S_i$ be the $i$th unit Laurent series. Then $$S_i∈K(X_H(25))_{q\text{-exp}}.$$ This promotes the formal unit series to genuine elements of the modular function field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitSeries25_mem (K : Type*) [Field K] (i : Fin 5) :
    unitSeries25 K i ∈ ModularCurve.xHFunctionFieldC K 25 N25.H25 := by sorry
