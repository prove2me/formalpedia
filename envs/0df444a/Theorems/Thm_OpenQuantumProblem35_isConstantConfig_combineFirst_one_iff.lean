-- Prove2me | Theorems.Thm_OpenQuantumProblem35_isConstantConfig_combineFirst_one_iff
-- name    : OpenQuantumProblem35.isConstantConfig_combineFirst_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:00.97441+00:00
-- url     : https://prove2.me/theorems/944f8a29-c523-5b0e-9b51-e15c6dc07d1f
-- title:
--   Open Quantum Problem35: is Constant Config combine First one iff
-- statement:
--   A configuration obtained by combining one entry with a tail is constant iff the tail is the constant completion of that entry.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L493-L511
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L493-L511

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.isConstantConfig_combineFirst_one_iff {n d : ℕ} (hn : 1 ≤ n)
    (x : Config 1 d) (z : Config (n - 1) d) :
    IsConstantConfig (combineFirst (n := n) (d := d) 1 hn x z) ↔
      z = constantCompletion (n := n) (d := d) x := by sorry
