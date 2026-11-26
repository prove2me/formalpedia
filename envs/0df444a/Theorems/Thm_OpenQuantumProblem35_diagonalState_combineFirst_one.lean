-- Prove2me | Theorems.Thm_OpenQuantumProblem35_diagonalState_combineFirst_one
-- name    : OpenQuantumProblem35.diagonalState_combineFirst_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:01.627141+00:00
-- url     : https://prove2.me/theorems/00792ca3-f4f0-509b-b407-2e5800d79348
-- title:
--   Open Quantum Problem35: diagonal State combine First one
-- statement:
--   The diagonal state on a split configuration is nonzero exactly on the graph of the constant completion map.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L514-L529
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L514-L529

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.diagonalState_combineFirst_one {n d : ℕ} (hn : 1 ≤ n)
    (x : Config 1 d) (z : Config (n - 1) d) :
    diagonalState n d (combineFirst (n := n) (d := d) 1 hn x z) =
      if z = constantCompletion (n := n) (d := d) x then uniformCoeff d else 0 := by sorry
