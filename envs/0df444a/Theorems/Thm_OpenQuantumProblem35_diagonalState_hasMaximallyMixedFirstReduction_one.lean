-- Prove2me | Theorems.Thm_OpenQuantumProblem35_diagonalState_hasMaximallyMixedFirstReduction_one
-- name    : OpenQuantumProblem35.diagonalState_hasMaximallyMixedFirstReduction_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:16.779388+00:00
-- url     : https://prove2.me/theorems/c430a419-01c6-5ae0-905e-9ff3ede0180b
-- title:
--   Open Quantum Problem35: diagonal State has Maximally Mixed First Reduction one
-- statement:
--   The diagonal state has maximally mixed one-party reductions once $n \ge 2$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L596-L606
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L596-L606

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.diagonalState_hasMaximallyMixedFirstReduction_one {n d : ℕ} (hn : 2 ≤ n) :
    HasMaximallyMixedFirstReduction (n := n) (d := d) 1 (by omega) (diagonalState n d) := by sorry
