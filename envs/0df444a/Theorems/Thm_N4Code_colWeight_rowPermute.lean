-- Prove2me | Theorems.Thm_N4Code_colWeight_rowPermute
-- name    : N4Code.colWeight_rowPermute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:15.832457+00:00
-- url     : https://prove2.me/theorems/f0c8946b-6f9f-5571-86ef-bc9dcd545c47
-- title:
--   N4 Code: col Weight row Permute
-- statement:
--   Row permutations preserve column weight.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L278-L289
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L278-L289

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colWeight_rowPermute (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    colWeight (rowPermute ρ c) = colWeight c := by sorry
