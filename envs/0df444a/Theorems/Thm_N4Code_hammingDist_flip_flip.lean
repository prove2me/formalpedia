-- Prove2me | Theorems.Thm_N4Code_hammingDist_flip_flip
-- name    : N4Code.hammingDist_flip_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:59.551592+00:00
-- url     : https://prove2.me/theorems/afe32c7b-a361-57c3-8634-3d581ec0e6a1
-- title:
--   N4 Code: hamming Dist flip flip
-- statement:
--   Flipping the same bit of both words preserves their distance.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L230-L235
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L230-L235

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.hammingDist_flip_flip {n : ℕ} (x y : Word n) (t : Fin n) :
    hammingDist (flipBit t x) (flipBit t y) = hammingDist x y := by sorry
