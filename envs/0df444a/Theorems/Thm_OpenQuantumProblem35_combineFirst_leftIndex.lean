-- Prove2me | Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
-- name    : OpenQuantumProblem35.combineFirst_leftIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:54.189135+00:00
-- url     : https://prove2.me/theorems/c759bf0f-e96a-45ea-9b76-0f8a70dc21d7
-- title:
--   Open Quantum Problem35: combine First left Index
-- statement:
--   Combining and then restricting to the left block recovers the left input.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L201-L204
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L201-L204

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.combineFirst_leftIndex {n d m : ℕ} (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) (i : Fin m) :
    combineFirst (n := n) (d := d) m hm x y (leftIndex hm i) = x i := by sorry
