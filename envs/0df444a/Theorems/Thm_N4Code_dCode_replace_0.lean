-- Prove2me | Theorems.Thm_N4Code_dCode_replace_0
-- name    : N4Code.dCode_replace_0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:38.521845+00:00
-- url     : https://prove2.me/theorems/ac567e2f-b7a1-41aa-a958-076fa658043f
-- title:
--   N4 Code: d Code replace 0
-- statement:
--   d_C'(y) = min(d_O(y), d_P(F_t y)) for the 0 → s' change (paper eq. dcp).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L294-L329
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L294-L329

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dCode_replace_0 {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n) :
    dCode (replaceColumn C t s') y = min (dOc C s' hO y) (dPc C s' hP (flipBit t y)) := by sorry
