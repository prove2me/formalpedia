-- Prove2me | Theorems.Thm_N4Code_universalStrictBetter_of_equivalent
-- name    : N4Code.universalStrictBetter_of_equivalent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:44.332792+00:00
-- url     : https://prove2.me/theorems/37965ba8-016c-5ae9-bcd1-4a804cb46ce4
-- title:
--   N4 Code: universal Strict Better of equivalent
-- statement:
--   Equivalent codes inherit strict universal domination.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L263-L270
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L263-L270

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

theorem N4Code.universalStrictBetter_of_equivalent {n : ℕ} (C₁ C₁' C₂ C₂' : Code n)
    (h1 : Equivalent C₁ C₁') (h2 : Equivalent C₂ C₂') (h : UniversalStrictBetter C₁' C₂') :
    UniversalStrictBetter C₁ C₂ := by sorry
