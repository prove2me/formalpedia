-- Prove2me | Theorems.Thm_N4Code_min4_perm
-- name    : N4Code.min4_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:32.916838+00:00
-- url     : https://prove2.me/theorems/44274f92-1da4-41f9-86d9-6d3659196aa5
-- title:
--   N4 Code: min4 perm
-- statement:
--   Permuting the four rows does not change the minimum distance.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L106-L128
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L106-L128

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

theorem N4Code.min4_perm (a : Fin 4 → ℕ) (ρ : Equiv (Fin 4) (Fin 4)) :
    min (a (ρ 0)) (min (a (ρ 1)) (min (a (ρ 2)) (a (ρ 3)))) =
      min (a 0) (min (a 1) (min (a 2) (a 3))) := by sorry
