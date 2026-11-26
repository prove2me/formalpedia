-- Prove2me | Theorems.Thm_OpenQuantumProblem35_not_existsAME_zero_dim
-- name    : OpenQuantumProblem35.not_existsAME_zero_dim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:37.80982+00:00
-- url     : https://prove2.me/theorems/b46cb937-6883-5c6c-97b9-f20a51eaecca
-- title:
--   Open Quantum Problem35: not exists AME zero dim
-- statement:
--   No absolutely maximally entangled state exists in local dimension $0$ once $n \ge 1$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L264-L272
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L264-L272

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.not_existsAME_zero_dim {n : ℕ} (hn : 1 ≤ n) : ¬ ExistsAME n 0 := by sorry
