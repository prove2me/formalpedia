-- Prove2me | Theorems.Thm_N4Code_zero_equal_off
-- name    : N4Code.zero_equal_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:12.165331+00:00
-- url     : https://prove2.me/theorems/87da8651-05fd-5e97-8905-07f7f6cced2e
-- title:
--   N4 Code: zero equal off
-- statement:
--   Words outside S keep their distance to the code under g0.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L450-L510
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L450-L510

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_equal_off {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n)
    (hnot : ¬ Y3c C s' hO hP t y) :
    dCode C y = dCode (replaceColumn C t s') (g0 C s' hO hP t y) := by sorry
