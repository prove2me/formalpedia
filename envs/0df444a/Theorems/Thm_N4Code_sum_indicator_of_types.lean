-- Prove2me | Theorems.Thm_N4Code_sum_indicator_of_types
-- name    : N4Code.sum_indicator_of_types
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:04.831572+00:00
-- url     : https://prove2.me/theorems/5c033a39-2ab3-53fc-a860-e890ab126ac3
-- title:
--   N4 Code: sum indicator of types
-- statement:
--   Group a per-position indicator sum by the types in S (all columns are in S).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L175-L196
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L175-L196

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code

theorem N4Code.sum_indicator_of_types {n : ℕ} (C : Code n) (S : Finset ℕ) (p : ℕ → Prop)
    [DecidablePred p] (hS : ∀ t : Fin n, colVal (C t) ∈ S) :
    (∑ t : Fin n, if p (colVal (C t)) then 1 else 0) =
      ∑ i ∈ S, count C i * (if p i then 1 else 0) := by sorry
