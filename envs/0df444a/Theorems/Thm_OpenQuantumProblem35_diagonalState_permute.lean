-- Prove2me | Theorems.Thm_OpenQuantumProblem35_diagonalState_permute
-- name    : OpenQuantumProblem35.diagonalState_permute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:47.360092+00:00
-- url     : https://prove2.me/theorems/1f514ba6-2102-4a58-99a5-2973b5797f98
-- title:
--   Open Quantum Problem35: diagonal State permute
-- statement:
--   The diagonal state is invariant under permutations of the parties.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L443-L452
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L443-L452

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.diagonalState_permute (n d : ℕ) (π : Equiv.Perm (Fin n)) :
    permuteState π (diagonalState n d) = diagonalState n d := by sorry
