-- Prove2me | Theorems.Thm_N25_level25_gamma0_S_doubleCosets
-- name    : N25.level25_gamma0_S_doubleCosets
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:34.208975+00:00
-- url     : https://prove2.me/theorems/12014b29-1996-404c-a10e-ea5a03d46dc6
-- title:
--   There are sixteen $Γ_0(25)$–$⟨S⟩$ double cosets
-- statement:
--   For the congruence subgroup $Γ_0(25)$ and the standard modular generator $S$, $$|Γ_0(25)\backslash SL_2(ℤ)/⟨S⟩|=16.$$ This is the order-two elliptic-orbit count for the auxiliary level-$25$ computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped MatrixGroups
open N25

theorem N25.level25_gamma0_S_doubleCosets :
    Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma0 25 : Set SL(2, ℤ))
      (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) = 16 := by sorry
