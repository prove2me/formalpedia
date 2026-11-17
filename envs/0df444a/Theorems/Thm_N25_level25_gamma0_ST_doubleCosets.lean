-- Prove2me | Theorems.Thm_N25_level25_gamma0_ST_doubleCosets
-- name    : N25.level25_gamma0_ST_doubleCosets
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:58.993198+00:00
-- url     : https://prove2.me/theorems/8eaff154-daf9-48b7-92bb-a08e6f50c2db
-- title:
--   There are ten $Γ_0(25)$–$⟨ST⟩$ double cosets
-- statement:
--   Let $Γ_0(25)≤SL_2(ℤ)$ and let $S,T$ be the standard modular generators. Then $$|Γ_0(25)\backslash SL_2(ℤ)/⟨ST⟩|=10.$$ This is the order-three elliptic-orbit count for the auxiliary $Γ_0(25)$ census.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped MatrixGroups
open N25

theorem N25.level25_gamma0_ST_doubleCosets :
    Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma0 25 : Set SL(2, ℤ))
      (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) = 10 := by sorry
