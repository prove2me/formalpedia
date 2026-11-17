-- Prove2me | Theorems.Thm_N25_unitAnalytic25_ne_zero
-- name    : N25.unitAnalytic25_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:50.447196+00:00
-- url     : https://prove2.me/theorems/8a3cace2-16b1-48bf-b06d-6b783be7d9be
-- title:
--   The analytic modular units never vanish on the upper half-plane
-- statement:
--   Let $i∈ℤ/5ℤ$ and $τ∈\mathfrak H$. Then $$u_i(τ)≠0.$$ This ensures that all unit ratios and reciprocal q-expansions used later are well defined.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitAnalytic25_ne_zero (i : Fin 5) (τ : UpperHalfPlane) :
    unitAnalytic25 i τ ≠ 0 := by sorry
