-- Prove2me | Theorems.Thm_N4Code_dRowMin_univ
-- name    : N4Code.dRowMin_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:30.314797+00:00
-- url     : https://prove2.me/theorems/063572aa-8f63-5014-ab11-c974b7100292
-- title:
--   N4 Code: d Row Min univ
-- statement:
--   dCode is the minimum over all four rows.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L57-L84
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L57-L84

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRowMin_univ {n : ℕ} (C : Code n) (y : Word n) :
    dRowMin C (Finset.univ : Finset (Fin 4)) (Finset.univ_nonempty) y = dCode C y := by sorry
