-- Prove2me | Theorems.Thm_N4Code_g0_involutive
-- name    : N4Code.g0_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:57.595875+00:00
-- url     : https://prove2.me/theorems/9f46ee7f-87c8-5c80-8462-025bfb83dd6f
-- title:
--   N4 Code: g0 involutive
-- statement:
--   g0 is an involution.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L360-L391
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L360-L391

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.g0_involutive {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) (hcol : C t = col0) :
    g0 C s' hO hP t (g0 C s' hO hP t y) = y := by sorry
