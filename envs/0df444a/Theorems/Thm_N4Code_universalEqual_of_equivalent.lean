-- Prove2me | Theorems.Thm_N4Code_universalEqual_of_equivalent
-- name    : N4Code.universalEqual_of_equivalent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:41.274555+00:00
-- url     : https://prove2.me/theorems/c4b85f72-ff77-4045-85f2-15338c596124
-- title:
--   N4 Code: universal Equal of equivalent
-- statement:
--   Equivalent codes have identical performance.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L257-L260
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L257-L260

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

theorem N4Code.universalEqual_of_equivalent {n : ℕ} (C C' : Code n) (h : Equivalent C C') :
    UniversalEqual C' C := by sorry
