-- Prove2me | Theorems.Thm_N4Code_hammingDist_mod2
-- name    : N4Code.hammingDist_mod2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:01.486112+00:00
-- url     : https://prove2.me/theorems/9f13591a-480e-4fd1-8809-406a9e1b367b
-- title:
--   N4 Code: hamming Dist mod2
-- statement:
--   Hamming distance is additive modulo two (triangle parity).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1920-L1930
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1920-L1930

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.hammingDist_mod2 {n : ℕ} (x y z : Word n) :
    hammingDist x z % 2 = (hammingDist x y + hammingDist y z) % 2 := by sorry
