-- Prove2me | Theorems.Thm_N4Code_odd_of_not_even
-- name    : N4Code.odd_of_not_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:59.882134+00:00
-- url     : https://prove2.me/theorems/ebace533-3823-4c2f-93c0-aead5f881779
-- title:
--   N4 Code: odd of not even
-- statement:
--   Not even means odd.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1438-L1439
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1438-L1439

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.odd_of_not_even {n : ℕ} (h : ¬ Even n) : Odd n := by sorry
