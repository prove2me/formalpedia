-- Prove2me | Theorems.Thm_N4Code_dCode_eq_min_dOc_dPc
-- name    : N4Code.dCode_eq_min_dOc_dPc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:36.470878+00:00
-- url     : https://prove2.me/theorems/f3a77b94-9997-56e8-99bf-37ada2fe8138
-- title:
--   N4 Code: d Code eq min d Oc d Pc
-- statement:
--   d_C(y) = min(d_O(y), d_P(y)) for the 0 → s' split.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L405-L419
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L405-L419

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dCode_eq_min_dOc_dPc {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (y : Word n) :
    dCode C y = min (dOc C s' hO y) (dPc C s' hP y) := by sorry
