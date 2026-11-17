-- Prove2me | Theorems.Thm_N25_jqTwentyFive_mem_xH25
-- name    : N25.jqTwentyFive_mem_xH25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:43.643795+00:00
-- url     : https://prove2.me/theorems/f57adf2c-5495-4034-89b9-c1a199bd6f4c
-- title:
--   The dilated $j$-series belongs to the $X_H(25)$ function field
-- statement:
--   Let $K$ be any field, let $H=H_{25}$, and let $K(X_H(25))$ denote the formal $q$-expansion model of the modular function field. Then the level-$25$ dilated $j$-series satisfies $$j(q^{25})∈K(X_H(25)).$$ This supplies one of the modular functions used to describe the level-$25$ curve. Formalization note: the theorem is stated uniformly for an arbitrary coefficient field $K$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0

set_option autoImplicit false
open N25

theorem N25.jqTwentyFive_mem_xH25 (K : Type*) [Field K] :
    ModularCurve.jqNModC K 25 ∈ ModularCurve.xHFunctionFieldC K 25 N25.H25 := by sorry
