-- Prove2me | Theorems.Thm_N25_level25_gamma0_index
-- name    : N25.level25_gamma0_index
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:19.990198+00:00
-- url     : https://prove2.me/theorems/aa657725-13fd-41bd-bdb0-2d38f21cd730
-- title:
--   The index of $Γ_0(25)$ is thirty
-- statement:
--   For the congruence subgroup $Γ_0(25)≤SL_2(ℤ)$, $$[SL_2(ℤ):Γ_0(25)]=30.$$ This is the base index used to compute the index of $Γ_H(25)$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped MatrixGroups
open N25

theorem N25.level25_gamma0_index : (CongruenceSubgroup.Gamma0 25).index = 30 := by sorry
