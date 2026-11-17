-- Prove2me | Theorems.Thm_N25_level25_S_doubleCosets
-- name    : N25.level25_S_doubleCosets
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:32.350059+00:00
-- url     : https://prove2.me/theorems/184c5ab5-e042-4d35-9563-8a33a1058070
-- title:
--   There are eighty $Γ_H(25)$–$⟨S⟩$ double cosets
-- statement:
--   Let $Γ=Γ_H(25)≤SL_2(ℤ)$ and let $S$ be the standard order-four modular generator. Then $$|Γ\backslash SL_2(ℤ)/⟨S⟩|=80.$$ This is the order-two elliptic-orbit count used in the genus and cusp calculation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped MatrixGroups
open N25

theorem N25.level25_S_doubleCosets :
    Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH 25 H25 : Set SL(2, ℤ))
      (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) = 80 := by sorry
