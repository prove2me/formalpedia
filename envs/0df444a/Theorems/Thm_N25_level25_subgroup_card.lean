-- Prove2me | Theorems.Thm_N25_level25_subgroup_card
-- name    : N25.level25_subgroup_card
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:45.587189+00:00
-- url     : https://prove2.me/theorems/d7ea8eb3-5d2d-43c3-b9dd-8e2fd1357ec2
-- title:
--   The subgroup $H_{25}$ has four elements
-- statement:
--   Let $H_{25}=⟨7⟩≤(ℤ/25ℤ)^×$. Then $$|H_{25}|=4.$$ This finite cardinality is used in the row-orbit and index computations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_subgroup_card : Nat.card H25 = 4 := by sorry
