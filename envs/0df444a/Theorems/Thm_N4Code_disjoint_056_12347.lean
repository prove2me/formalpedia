-- Prove2me | Theorems.Thm_N4Code_disjoint_056_12347
-- name    : N4Code.disjoint_056_12347
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:36.678255+00:00
-- url     : https://prove2.me/theorems/225b2566-a86b-5fbe-a64a-4abcffef9d0f
-- title:
--   N4 Code: disjoint 056 12347
-- statement:
--   The sets {0,5,6} and {1,2,3,4,7} are disjoint.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1505-L1509
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1505-L1509

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.disjoint_056_12347 : Disjoint ({0, 5, 6} : Finset ℕ) ({1, 2, 3, 4, 7} : Finset ℕ) := by sorry
