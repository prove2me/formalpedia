-- Prove2me | Theorems.Thm_N4Code_alpha_equiv
-- name    : N4Code.alpha_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:35.726437+00:00
-- url     : https://prove2.me/theorems/b93881ed-c69a-4974-b38a-ed1bd9c3e5b6
-- title:
--   N4 Code: alpha equiv
-- statement:
--   α is invariant under equivalence.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L214-L232
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L214-L232

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

theorem N4Code.alpha_equiv {n : ℕ} (C C' : Code n) (h : Equivalent C C') (d : ℕ) :
    alpha C' d = alpha C d := by sorry
