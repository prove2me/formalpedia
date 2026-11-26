-- Prove2me | Theorems.Thm_N4Code_flipCol_involutive
-- name    : N4Code.flipCol_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:39.135994+00:00
-- url     : https://prove2.me/theorems/4c8adf58-32f7-5b3d-90ce-ed79afb0ecf9
-- title:
--   N4 Code: flip Col involutive
-- statement:
--   `flipCol` is an involution.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2294-L2296
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2294-L2296

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.flipCol_involutive (c : Column) : flipCol (flipCol c) = c := by sorry
