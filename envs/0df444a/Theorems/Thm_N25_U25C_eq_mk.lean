-- Prove2me | Theorems.Thm_N25_U25C_eq_mk
-- name    : N25.U25C_eq_mk
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:47.330788+00:00
-- url     : https://prove2.me/theorems/dc5de165-e226-4be1-8a38-8f15c4bc3670
-- title:
--   Each modular unit is the prescribed series with its membership certificate
-- statement:
--   Let $K$ be a field and let $i\in\mathbb Z/5\mathbb Z$. If $u_i$ is the prescribed Laurent series and $h_i$ is its certificate of membership in the level-$25$ function field, then the modular unit is the corresponding bundled element:
--
--   $$U_i=(u_i,h_i).$$
--
--   This unfolds the bundled function-field element used throughout the unit calculations. Formalization note: the second component is a proof certificate and carries no additional mathematical data.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Theorems.Thm_N25_unitSeries25_mem
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.U25C_eq_mk (K : Type*) [Field K] (i : Fin 5) :
    U25C K i = ⟨unitSeries25 K i, unitSeries25_mem K i⟩ := by sorry
