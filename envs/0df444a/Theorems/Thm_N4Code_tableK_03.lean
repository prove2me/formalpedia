-- Prove2me | Theorems.Thm_N4Code_tableK_03
-- name    : N4Code.tableK_03
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:53.766331+00:00
-- url     : https://prove2.me/theorems/4f9bc8a5-85dd-5e11-8a5d-98487a041d1c
-- title:
--   N4 Code: table K 03
-- statement:
--   The N4 Code construction uses the table K 03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1353-L1355
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1353-L1355

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.tableK_03 (a4 a5 a6 a7 : ℕ) :
    tableK a4 a5 a6 a7 1 = 0 ∧ tableK a4 a5 a6 a7 2 = 0 ∧ tableK a4 a5 a6 a7 3 = 0 := by sorry
