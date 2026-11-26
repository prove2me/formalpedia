-- Prove2me | Theorems.Thm_N4Code_zero_closer
-- name    : N4Code.zero_closer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:05.76661+00:00
-- url     : https://prove2.me/theorems/f7f3cb86-4ee7-5609-9e1e-3b5b9e954023
-- title:
--   N4 Code: zero closer
-- statement:
--   Words in S (paper eq. 6) come one step closer under the new code.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L422-L447
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L422-L447

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_closer {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) (y : Word n)
    (hS : Y3c C s' hO hP t y) :
    dCode C y = dCode (replaceColumn C t s') (g0 C s' hO hP t y) + 1 := by sorry
