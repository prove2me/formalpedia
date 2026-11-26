-- Prove2me | Theorems.Thm_N4Code_dRow_ge_two_of_mismatch
-- name    : N4Code.dRow_ge_two_of_mismatch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:00.486118+00:00
-- url     : https://prove2.me/theorems/f8eee9a6-4097-4601-bfc3-0e5bee345ee8
-- title:
--   N4 Code: d Row ge two of mismatch
-- statement:
--   If y differs from row j at two distinct positions, the row distance is
--   at least 2.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1279-L1300
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1279-L1300

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow_ge_two_of_mismatch {n : ℕ} (C : Code n) (j : Fin 4) (t₁ t₂ : Fin n)
    (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : y t₁ ≠ row C j t₁) (h2 : y t₂ ≠ row C j t₂) : 2 ≤ dRow C j y := by sorry
