-- Prove2me | Theorems.Thm_N4Code_rowPermute_col0
-- name    : N4Code.rowPermute_col0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:38.787804+00:00
-- url     : https://prove2.me/theorems/524fed8c-013e-5a97-9b3c-8bef0c7685b4
-- title:
--   N4 Code: row Permute col0
-- statement:
--   The zero column is fixed by any row permutation.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2214-L2216
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2214-L2216

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.rowPermute_col0 (ρ : Equiv (Fin 4) (Fin 4)) : rowPermute ρ col0 = col0 := by sorry
