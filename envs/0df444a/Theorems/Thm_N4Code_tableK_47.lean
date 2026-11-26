-- Prove2me | Theorems.Thm_N4Code_tableK_47
-- name    : N4Code.tableK_47
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:26.544953+00:00
-- url     : https://prove2.me/theorems/e743e774-0ad2-539c-b16e-e9e185de8413
-- title:
--   N4 Code: table K 47
-- statement:
--   The N4 Code construction uses the table K 47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1357-L1360
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1357-L1360

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.tableK_47 (a4 a5 a6 a7 : ℕ) :
    tableK a4 a5 a6 a7 4 = a4 ∧ tableK a4 a5 a6 a7 5 = a5 ∧
      tableK a4 a5 a6 a7 6 = a6 ∧ tableK a4 a5 a6 a7 7 = a7 := by sorry
