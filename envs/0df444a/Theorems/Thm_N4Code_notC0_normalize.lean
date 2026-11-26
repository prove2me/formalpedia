-- Prove2me | Theorems.Thm_N4Code_notC0_normalize
-- name    : N4Code.notC0_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:18.941422+00:00
-- url     : https://prove2.me/theorems/d8caf08a-64b1-5191-bb5b-64915e981215
-- title:
--   N4 Code: not C0 normalize
-- statement:
--   The normalized code is not in the C0 form.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2130-L2134
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2130-L2134

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.notC0_normalize {n : ℕ} (C : Code n) (i j : Fin 4)
    (hC0 : ¬ ∃ C0 : Code n, Equivalent C C0 ∧ C0form C0) :
    ¬ C0form (normalizeCode C i j) := by sorry
