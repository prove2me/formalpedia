-- Prove2me | Theorems.Thm_N4Code_dRow12_columns07
-- name    : N4Code.dRow12_columns07
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:24.859739+00:00
-- url     : https://prove2.me/theorems/8f30da34-14fc-4aa5-a4a1-c99af67bc51d
-- title:
--   N4 Code: d Row12 columns07
-- statement:
--   d₁ and d₂ in terms of the per-type weights for a Columns07 code.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L896-L942
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L896-L942

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow12_columns07 {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C) :
    dRow C 1 y = w_i C 0 y + w_i C 1 y + w_i C 2 y + w_i C 3 y +
      (count C 4 - w_i C 4 y) + (count C 5 - w_i C 5 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) ∧
    dRow C 2 y = w_i C 0 y + w_i C 1 y + w_i C 4 y + w_i C 5 y +
      (count C 2 - w_i C 2 y) + (count C 3 - w_i C 3 y) +
      (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y) := by sorry
