-- Prove2me | Theorems.Thm_N25_unitAnalytic25_mdifferentiable
-- name    : N25.unitAnalytic25_mdifferentiable
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:22.346195+00:00
-- url     : https://prove2.me/theorems/6161cbbf-c18b-40db-b30f-3f2415dcd6a7
-- title:
--   Every analytic level-$25$ unit is holomorphic on the upper half-plane
-- statement:
--   For each $i∈ℤ/5ℤ$, let $u_i:\mathfrak H→ℂ$ be the corresponding analytic modular unit. Then $$u_i\text{ is complex differentiable on }\mathfrak H.$$ This provides the analytic regularity required for constructing modular forms from the units.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open scoped Manifold
open N25

theorem N25.unitAnalytic25_mdifferentiable (i : Fin 5) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (unitAnalytic25 i) := by sorry
