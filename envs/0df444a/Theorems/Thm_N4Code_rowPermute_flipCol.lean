-- Prove2me | Theorems.Thm_N4Code_rowPermute_flipCol
-- name    : N4Code.rowPermute_flipCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:46.929938+00:00
-- url     : https://prove2.me/theorems/f78bb225-1e55-460d-830c-3b9c7969b774
-- title:
--   N4 Code: row Permute flip Col
-- statement:
--   Row permutations and flips commute.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2299-L2302
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2299-L2302

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.rowPermute_flipCol (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ (flipCol c) = flipCol (rowPermute ρ c) := by sorry
