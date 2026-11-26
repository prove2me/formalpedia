-- Prove2me | Theorems.Thm_N4Code_hammingWeight_swapBits
-- name    : N4Code.hammingWeight_swapBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:35.726747+00:00
-- url     : https://prove2.me/theorems/e3cf2639-eda2-51d7-9430-f089f96e4e9f
-- title:
--   N4 Code: hamming Weight swap Bits
-- statement:
--   Swapping two bits does not change the Hamming weight.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2249-L2273
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2249-L2273

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.hammingWeight_swapBits {n : ℕ} (t₁ t' : Fin n) (z : Word n) :
    hammingWeight (swapBits t₁ t' z) = hammingWeight z := by sorry
