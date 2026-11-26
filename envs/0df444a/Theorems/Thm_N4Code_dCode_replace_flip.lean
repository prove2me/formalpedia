-- Prove2me | Theorems.Thm_N4Code_dCode_replace_flip
-- name    : N4Code.dCode_replace_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:24.761396+00:00
-- url     : https://prove2.me/theorems/153b9eb6-fc91-45fe-9138-151e9c47f9b4
-- title:
--   N4 Code: d Code replace flip
-- statement:
--   d_{C'}(F_1 y) = min(d_O'(y), d_P(y)) (paper eq. dcpf).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L204-L208
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L204-L208

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.dCode_replace_flip {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    dCode (replaceColumn C t col3) (flipBit t y) = min (dOp C t y) (dP C y) := by sorry
