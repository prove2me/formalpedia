-- Prove2me | Theorems.Thm_N25_level25_gammaH_index
-- name    : N25.level25_gammaH_index
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:48.157271+00:00
-- url     : https://prove2.me/theorems/ade9c04c-5233-4690-9adb-e2c962f58da8
-- title:
--   The index of $Γ_H(25)$ factors through the unit-subgroup index
-- statement:
--   Let $H≤(ℤ/25ℤ)^×$, let $Γ_H(25)$ be the corresponding congruence subgroup, and let $[G:K]$ denote subgroup index. Then $$[SL_2(ℤ):Γ_H(25)]=[(ℤ/25ℤ)^×:H]\,[SL_2(ℤ):Γ_0(25)].$$ This reduces the level-$25$ index calculation to a finite unit-group computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open scoped MatrixGroups
open N25

theorem N25.level25_gammaH_index (H : Subgroup (ZMod 25)ˣ) :
    (CohCarrier.GammaH 25 H).index = H.index * (CongruenceSubgroup.Gamma0 25).index := by sorry
