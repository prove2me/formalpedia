-- Prove2me | Theorems.Thm_N4Code_colVal_rowPermute_flipCol5
-- name    : N4Code.colVal_rowPermute_flipCol5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:34.8758+00:00
-- url     : https://prove2.me/theorems/83355425-8bdc-404d-bc09-5c6abd4aba76
-- title:
--   N4 Code: col Val row Permute flip Col5
-- statement:
--   Row-permuting the flip of the type-5 column gives a two-bit column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2184-L2204
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2184-L2204

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colVal_rowPermute_flipCol5 (ρ : Equiv (Fin 4) (Fin 4)) :
    colVal (rowPermute ρ (flipCol col5)) = 3 ∨ colVal (rowPermute ρ (flipCol col5)) = 5 ∨
      colVal (rowPermute ρ (flipCol col5)) = 6 ∨ colVal (rowPermute ρ (flipCol col5)) = 9 ∨
      colVal (rowPermute ρ (flipCol col5)) = 10 ∨ colVal (rowPermute ρ (flipCol col5)) = 12 := by sorry
