-- Prove2me | Theorems.Thm_N4Code_dRow03_columns07
-- name    : N4Code.dRow03_columns07
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:39.11562+00:00
-- url     : https://prove2.me/theorems/31824ba4-d389-46e6-97b3-e146db55012d
-- title:
--   N4 Code: d Row03 columns07
-- statement:
--   d₀ and d₄ in terms of the per-type weights for a Columns07 code.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1375-L1419
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1375-L1419

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow03_columns07 {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C) :
    dRow C 0 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y + w_i C 4 y +
      w_i C 5 y + w_i C 6 y + w_i C 7 y ∧
    dRow C 3 y = w_i C 0 y + w_i C 2 y + w_i C 4 y + w_i C 6 y +
      (count C 1 - w_i C 1 y) + (count C 3 - w_i C 3 y) +
      (count C 5 - w_i C 5 y) + (count C 7 - w_i C 7 y) := by sorry
