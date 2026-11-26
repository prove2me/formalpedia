-- Prove2me | Theorems.Thm_N4Code_rowPermute_symm
-- name    : N4Code.rowPermute_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:27.143022+00:00
-- url     : https://prove2.me/theorems/d5d60b17-8330-5d1e-a426-f0d23d2c1b35
-- title:
--   N4 Code: row Permute symm
-- statement:
--   Row permutation composed with its inverse is the identity.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2208-L2211
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2208-L2211

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.rowPermute_symm (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ (rowPermute ρ.symm c) = c := by sorry
