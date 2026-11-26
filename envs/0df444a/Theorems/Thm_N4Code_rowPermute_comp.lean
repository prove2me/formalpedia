-- Prove2me | Theorems.Thm_N4Code_rowPermute_comp
-- name    : N4Code.rowPermute_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:39.743866+00:00
-- url     : https://prove2.me/theorems/3ef03e8c-81f3-5fec-a37b-5e5c9a1407e7
-- title:
--   N4 Code: row Permute comp
-- statement:
--   Row-permutation composition.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2276-L2279
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2276-L2279

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.rowPermute_comp (ρ₁ ρ₂ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ₁ (rowPermute ρ₂ c) = rowPermute (ρ₁.trans ρ₂) c := by sorry
