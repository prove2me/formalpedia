-- Prove2me | Theorems.Thm_N4Code_even_weight_iff
-- name    : N4Code.even_weight_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:56.853332+00:00
-- url     : https://prove2.me/theorems/66c96646-a467-480d-826c-82be187f110b
-- title:
--   N4 Code: even weight iff
-- statement:
--   A weight differing by the flip relation preserves parity.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L316-L330
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L316-L330

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

theorem N4Code.even_weight_iff {a b : ℕ} (h : b = a ∨ b = 4 - a) (ha4 : a ≤ 4) (hb4 : b ≤ 4) :
    Even b ↔ Even a := by sorry
