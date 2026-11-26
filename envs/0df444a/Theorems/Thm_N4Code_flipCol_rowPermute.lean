-- Prove2me | Theorems.Thm_N4Code_flipCol_rowPermute
-- name    : N4Code.flipCol_rowPermute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:36.792803+00:00
-- url     : https://prove2.me/theorems/69e0f8e5-1ad2-42f5-b3ca-5c94f0acdc2d
-- title:
--   N4 Code: flip Col row Permute
-- statement:
--   Flipping commutes with row permutation.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2288-L2291
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2288-L2291

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.flipCol_rowPermute (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    flipCol (rowPermute ρ c) = rowPermute ρ (flipCol c) := by sorry
