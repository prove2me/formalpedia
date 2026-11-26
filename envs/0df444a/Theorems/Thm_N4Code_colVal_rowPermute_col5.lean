-- Prove2me | Theorems.Thm_N4Code_colVal_rowPermute_col5
-- name    : N4Code.colVal_rowPermute_col5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:27.75659+00:00
-- url     : https://prove2.me/theorems/6a97e92e-5cb5-42e9-872d-353587fef361
-- title:
--   N4 Code: col Val row Permute col5
-- statement:
--   Row-permuting the type-5 column gives a two-bit column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2155-L2176
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2155-L2176

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colVal_rowPermute_col5 (ρ : Equiv (Fin 4) (Fin 4)) :
    colVal (rowPermute ρ col5) = 3 ∨ colVal (rowPermute ρ col5) = 5 ∨
      colVal (rowPermute ρ col5) = 6 ∨ colVal (rowPermute ρ col5) = 9 ∨
      colVal (rowPermute ρ col5) = 10 ∨ colVal (rowPermute ρ col5) = 12 := by sorry
