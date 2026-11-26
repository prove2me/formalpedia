-- Prove2me | Theorems.Thm_N4Code_rowPermute_left_inv
-- name    : N4Code.rowPermute_left_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:43.398802+00:00
-- url     : https://prove2.me/theorems/7629f938-e20c-459f-abe1-aed3cdb21fb8
-- title:
--   N4 Code: row Permute left inv
-- statement:
--   Row-permuting by ρ then ρ⁻¹ is the identity.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2282-L2285
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2282-L2285

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.rowPermute_left_inv (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ.symm (rowPermute ρ c) = c := by sorry
