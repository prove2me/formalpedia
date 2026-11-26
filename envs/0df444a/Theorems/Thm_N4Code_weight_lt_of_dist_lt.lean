-- Prove2me | Theorems.Thm_N4Code_weight_lt_of_dist_lt
-- name    : N4Code.weight_lt_of_dist_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:16.673516+00:00
-- url     : https://prove2.me/theorems/c6420645-ae44-5f82-a09e-c5583f3af3d1
-- title:
--   N4 Code: weight lt of dist lt
-- statement:
--   Distance-comparison form used by `thm:com` (Lemma 18): closer words contribute more.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L80-L83
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L80-L83

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

theorem N4Code.weight_lt_of_dist_lt {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {a b : ℕ} (h : a < b) :
    (1 - ε) ^ (n - b) * ε ^ b < (1 - ε) ^ (n - a) * ε ^ a := by sorry
