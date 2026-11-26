-- Prove2me | Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
-- name    : OpenQuantumProblem35.diagonalState_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:53.461829+00:00
-- url     : https://prove2.me/theorems/658dc4f0-0114-5051-953a-1a522aad453c
-- title:
--   Open Quantum Problem35: diagonal State apply
-- statement:
--   Evaluating the diagonal state returns the uniform coefficient on constant strings and `0` otherwise.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L326-L328
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L326-L328

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.diagonalState_apply {n d : ℕ} (x : Config n d) :
    diagonalState n d x = if IsConstantConfig x then uniformCoeff d else 0 := by sorry
