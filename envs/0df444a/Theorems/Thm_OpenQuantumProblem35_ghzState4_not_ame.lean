-- Prove2me | Theorems.Thm_OpenQuantumProblem35_ghzState4_not_ame
-- name    : OpenQuantumProblem35.ghzState4_not_ame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:13.745369+00:00
-- url     : https://prove2.me/theorems/c75f783b-a348-56c3-bae6-d6f74b826d7c
-- title:
--   Open Quantum Problem35: ghz State4 not ame
-- statement:
--   Sanity check: the standard GHZ family on $4$ parties is not absolutely maximally entangled for any local dimension $d \ge 2$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L658-L696
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L658-L696

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.ghzState4_not_ame {d : ℕ} (hd : 2 ≤ d) :
    ¬ IsAME (n := 4) (d := d) (ghzState4 d) := by sorry
