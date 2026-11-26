-- Prove2me | Theorems.Thm_N4Code_hammingWeight_xor_mod2
-- name    : N4Code.hammingWeight_xor_mod2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:57.048669+00:00
-- url     : https://prove2.me/theorems/48a25118-06dd-4015-97a2-50f95b670cb9
-- title:
--   N4 Code: hamming Weight xor mod2
-- statement:
--   The weight of an XOR is additive modulo two.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1904-L1917
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1904-L1917

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.hammingWeight_xor_mod2 {n : ℕ} (x y : Word n) :
    hammingWeight (bitXor x y) % 2 = (hammingWeight x + hammingWeight y) % 2 := by sorry
