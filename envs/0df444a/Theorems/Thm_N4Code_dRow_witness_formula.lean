-- Prove2me | Theorems.Thm_N4Code_dRow_witness_formula
-- name    : N4Code.dRow_witness_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:31.103389+00:00
-- url     : https://prove2.me/theorems/93788ec2-2e00-42a8-afd3-c4477ab063b7
-- title:
--   N4 Code: d Row witness formula
-- statement:
--   The N4 Code construction uses the d Row witness formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1138-L1203
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1138-L1203

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRow_witness_formula {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C)
    (hw123 : w_i C 1 y = 0 ∧ w_i C 2 y = 0 ∧ w_i C 3 y = 0)
    (_hw815 : ∀ i ∈ Finset.Icc 8 15, w_i C i y = 0) :
    dRow C 0 y = w_i C 0 y + w_i C 4 y + w_i C 5 y + w_i C 6 y + w_i C 7 y ∧
    dRow C 1 y = w_i C 0 y + (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 2 y = w_i C 0 y + count C 2 + count C 3 + w_i C 4 y + w_i C 5 y +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 3 y = w_i C 0 y + count C 1 + count C 3 + w_i C 4 y + (count C 5 - w_i C 5 y) +
      w_i C 6 y + (count C 7 - w_i C 7 y) := by sorry
