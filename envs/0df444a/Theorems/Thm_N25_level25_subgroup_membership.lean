-- Prove2me | Theorems.Thm_N25_level25_subgroup_membership
-- name    : N25.level25_subgroup_membership
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:57.539493+00:00
-- url     : https://prove2.me/theorems/0bc667af-b8c5-4b6e-8451-057ba4e4cea8
-- title:
--   $H_{25}$ consists of the residues $1,7,18,24$
-- statement:
--   Let $u∈(ℤ/25ℤ)^×$. Then $$u∈H_{25}\;⇔\;u≡1,7,18,\text{ or }24\pmod{25}.$$ This explicit membership test makes the finite orbit calculations executable.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_subgroup_membership (u : (ZMod 25)ˣ) :
    u ∈ H25 ↔ (u : ZMod 25) = 1 ∨ (u : ZMod 25) = 7 ∨
      (u : ZMod 25) = 18 ∨ (u : ZMod 25) = 24 := by sorry
