-- Prove2me | Theorems.Thm_OpenQuantumProblem35_constantCompletion_eq_iff
-- name    : OpenQuantumProblem35.constantCompletion_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:59:36.385929+00:00
-- url     : https://prove2.me/theorems/fbbda361-22cc-55dc-bae4-66c93b661f17
-- title:
--   Open Quantum Problem35: constant Completion eq iff
-- statement:
--   A tail configuration equals the constant completion of $x$ iff all of its entries agree with the unique entry of $x$.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L455-L462
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Defs.lean#L455-L462

module
public import Mathlib
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35

theorem OpenQuantumProblem35.constantCompletion_eq_iff {n d : ℕ} (x : Config 1 d) (z : Config (n - 1) d) :
    z = constantCompletion (n := n) (d := d) x ↔ ∀ i, z i = x 0 := by sorry
