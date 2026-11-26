-- Prove2me | Theorems.Thm_N4Code_bool_ne_cases
-- name    : N4Code.bool_ne_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:49.409244+00:00
-- url     : https://prove2.me/theorems/a676933f-5c24-4e94-821a-9483087da46a
-- title:
--   N4 Code: bool ne cases
-- statement:
--   A Boolean inequality is one of the two orientations.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L33-L41
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L33-L41

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.bool_ne_cases {a b : Bool} (h : a ≠ b) :
    (a = true ∧ b = false) ∨ (a = false ∧ b = true) := by sorry
