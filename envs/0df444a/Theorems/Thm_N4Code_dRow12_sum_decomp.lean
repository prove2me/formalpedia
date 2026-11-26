-- Prove2me | Theorems.Thm_N4Code_dRow12_sum_decomp
-- name    : N4Code.dRow12_sum_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:07.376926+00:00
-- url     : https://prove2.me/theorems/1cb63b6b-507c-4b6e-aaa5-589528e94e03
-- title:
--   N4 Code: d Row12 sum decomp
-- statement:
--   d₁ + d₂ = |2|+|3|+|4|+|5| + 2·K (parity of the sum of the two row
--   distances is the parity of |2|+|3|+|4|+|5|).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L946-L958
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L946-L958

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow12_sum_decomp {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C) :
    dRow C 1 y + dRow C 2 y =
      count C 2 + count C 3 + count C 4 + count C 5 +
        2 * (w_i C 0 y + w_i C 1 y + (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y)) := by sorry
