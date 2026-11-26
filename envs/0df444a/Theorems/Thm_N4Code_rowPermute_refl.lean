-- Prove2me | Theorems.Thm_N4Code_rowPermute_refl
-- name    : N4Code.rowPermute_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:08.537137+00:00
-- url     : https://prove2.me/theorems/3926ee92-ac2d-482f-a2ba-5b2af19c69eb
-- title:
--   N4 Code: row Permute refl
-- statement:
--   Row-permuting by the identity is the identity.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L878-L880
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L878-L880

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.rowPermute_refl (c : Column) : rowPermute (Equiv.refl (Fin 4)) c = c := by sorry
