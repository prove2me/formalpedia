-- Prove2me | Theorems.Thm_N4Code_min4_eq_image
-- name    : N4Code.min4_eq_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:24.06431+00:00
-- url     : https://prove2.me/theorems/260515fc-714e-44f4-9e7c-c928cdecc3c5
-- title:
--   N4 Code: min4 eq image
-- statement:
--   The nested four-fold minimum equals the minimum over the image set.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L88-L103
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L88-L103

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

theorem N4Code.min4_eq_image (a : Fin 4 → ℕ) :
    min (a 0) (min (a 1) (min (a 2) (a 3))) = (Finset.univ.image a).min' (by simp) := by sorry
