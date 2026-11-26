-- Prove2me | Theorems.Thm_N4Code_colWeight_flip
-- name    : N4Code.colWeight_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:22.258821+00:00
-- url     : https://prove2.me/theorems/683f4642-5d9c-4298-a3a3-c71f79e8f3f9
-- title:
--   N4 Code: col Weight flip
-- statement:
--   Column flips change weight w to 4 − w.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L293-L294
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L293-L294

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colWeight_flip : ∀ c : Column, colWeight (flipCol c) = 4 - colWeight c := by sorry
