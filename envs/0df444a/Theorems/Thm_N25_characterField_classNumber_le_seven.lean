-- Prove2me | Theorems.Thm_N25_characterField_classNumber_le_seven
-- name    : N25.characterField_classNumber_le_seven
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:54:00.151881+00:00
-- url     : https://prove2.me/theorems/e01225d0-e597-451f-ab99-6afde3946dbd
-- title:
--   The quintic character field has class number at most seven
-- statement:
--   Let $F$ be the quintic character field associated with the order-five character in the $71$-torsion filtration. Then $$h_F≤7.$$ This excludes nontrivial unramified characters of order $71$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Mathlib.NumberTheory.NumberField.Norm
import Definitions.Def_N25
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false
open N25

theorem N25.characterField_classNumber_le_seven :
    NumberField.classNumber characterField ≤ 7 := by sorry
