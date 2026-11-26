-- Prove2me | Theorems.Thm_N4Code_colWeight_le_4
-- name    : N4Code.colWeight_le_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:27.440867+00:00
-- url     : https://prove2.me/theorems/968c32fc-db8d-519b-a6ba-3ff9471671e4
-- title:
--   N4 Code: col Weight le 4
-- statement:
--   Column weights are at most 4.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L298-L299
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L298-L299

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

theorem N4Code.colWeight_le_4 : ∀ c : Column, colWeight c ≤ 4 := by sorry
