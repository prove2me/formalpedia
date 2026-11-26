-- Prove2me | Theorems.Thm_N4Code_hammingDist_set_bit
-- name    : N4Code.hammingDist_set_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:02.14744+00:00
-- url     : https://prove2.me/theorems/de9c52ac-1df2-4ba0-8111-2a00ef74672e
-- title:
--   N4 Code: hamming Dist set bit
-- statement:
--   Replacing the t-th bit of x by b changes the distance to y exactly as
--   flipping y's t-th bit when b = true, and not at all when b = false.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L239-L259
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L239-L259

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.hammingDist_set_bit {n : ℕ} (x : Word n) (t : Fin n) (y : Word n) (b : Bool)
    (hx0 : x t = false) :
    hammingDist (fun u => if u = t then b else x u) y =
      if b = true then hammingDist x (flipBit t y) else hammingDist x y := by sorry
