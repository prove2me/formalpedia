-- Prove2me | Theorems.Thm_N4Code_tableK_815
-- name    : N4Code.tableK_815
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:54.15241+00:00
-- url     : https://prove2.me/theorems/9cd41cf3-7b69-5063-97ee-0c798928b2fe
-- title:
--   N4 Code: table K 815
-- statement:
--   The N4 Code construction uses the table K 815 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1362-L1374
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1362-L1374

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.tableK_815 (a4 a5 a6 a7 : ℕ) : ∀ i ∈ Finset.Icc 8 15, tableK a4 a5 a6 a7 i = 0 := by sorry
