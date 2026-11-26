-- Prove2me | Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
-- name    : OpenQuantumProblem35.combineFirst_rightIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:59.540805+00:00
-- url     : https://prove2.me/theorems/0f01a8fa-4fdf-4a57-a189-59defeebe9fb
-- title:
--   Open Quantum Problem35: combine First right Index
-- statement:
--   Combining and then restricting to the right block recovers the right input.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L208-L212
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L208-L212

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.combineFirst_rightIndex {n d m : ℕ} (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) (i : Fin (n - m)) :
    combineFirst (n := n) (d := d) m hm x y (rightIndex hm i) = y i := by sorry
