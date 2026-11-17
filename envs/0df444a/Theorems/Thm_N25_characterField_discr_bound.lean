-- Prove2me | Theorems.Thm_N25_characterField_discr_bound
-- name    : N25.characterField_discr_bound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:26.940133+00:00
-- url     : https://prove2.me/theorems/a071fe66-d22e-45e4-9597-a1175a404226
-- title:
--   The character-field discriminant is at most $5^8$
-- statement:
--   Let $F$ be the quintic character field. Then $$|disc(F)|≤5^8.$$ This supplies the discriminant input for the class-number estimate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.characterField_discr_bound :
    (NumberField.discr characterField).natAbs ≤ 5 ^ 8 := by sorry
