-- Prove2me | Theorems.Thm_OpenQuantumProblem35_diagonalState_combineFirst_two_of_ne
-- name    : OpenQuantumProblem35.diagonalState_combineFirst_two_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:33.59586+00:00
-- url     : https://prove2.me/theorems/c8d7b368-979d-5303-9e6c-73da7bfd93bd
-- title:
--   Open Quantum Problem35: diagonal State combine First two of ne
-- statement:
--   On $4$ parties, the diagonal state vanishes on any split configuration whose first two entries are different.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L645-L655
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L645-L655

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.diagonalState_combineFirst_two_of_ne {d : ℕ} {x z : Config 2 d}
    (h : x 0 ≠ x 1) :
    diagonalState 4 d (combineFirst (n := 4) (d := d) 2 (by decide) x z) = 0 := by sorry
