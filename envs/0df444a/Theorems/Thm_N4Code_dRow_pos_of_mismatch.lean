-- Prove2me | Theorems.Thm_N4Code_dRow_pos_of_mismatch
-- name    : N4Code.dRow_pos_of_mismatch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:04.392324+00:00
-- url     : https://prove2.me/theorems/2e842ee5-049b-5349-8be6-0d205e121117
-- title:
--   N4 Code: d Row pos of mismatch
-- statement:
--   If y differs from row j at one position, the row distance is at least 1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1266-L1275
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1266-L1275

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow_pos_of_mismatch {n : ℕ} (C : Code n) (j : Fin 4) (t : Fin n) (y : Word n)
    (h : y t ≠ row C j t) : 1 ≤ dRow C j y := by sorry
