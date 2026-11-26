-- Prove2me | Theorems.Thm_N4Code_bool_xor_eq_true
-- name    : N4Code.bool_xor_eq_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:57.321583+00:00
-- url     : https://prove2.me/theorems/b860200b-8831-4e87-adb2-d6340ef69fea
-- title:
--   N4 Code: bool xor eq true
-- statement:
--   The N4 Code construction uses the bool xor eq true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L276-L277
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L276-L277

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

theorem N4Code.bool_xor_eq_true (a b : Bool) : Bool.xor a b = true ↔ a ≠ b := by sorry
