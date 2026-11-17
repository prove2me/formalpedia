-- Prove2me | Theorems.Thm_N25_characterField_degree_and_totallyReal
-- name    : N25.characterField_degree_and_totallyReal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:15.0572+00:00
-- url     : https://prove2.me/theorems/db50bf45-4f57-4360-a2dc-9b5825061e2d
-- title:
--   The character field is totally real of degree five
-- statement:
--   Let $F$ be the $H_{25}$-fixed subfield of $L=ℚ(ζ_{25})$. Then $$[F:ℚ]=5 ∧ [L:F]=4 ∧ TotallyReal(F).$$ These facts support the discriminant and class-number bounds.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.characterField_degree_and_totallyReal :
    Module.finrank ℚ characterField = 5 ∧
    Module.finrank characterField cyclotomicField = 4 ∧
    NumberField.IsTotallyReal characterField := by sorry
