-- Prove2me | Theorems.Thm_N4Code_z_34_implies_not_A
-- name    : N4Code.z_34_implies_not_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:38.293543+00:00
-- url     : https://prove2.me/theorems/3d74d888-f565-5084-a5a1-3e3b72b42ee2
-- title:
--   N4 Code: z 34 implies not A
-- statement:
--   Z3 ∪ Z4 is disjoint from Z1 ∪ Z2 ∪ Z5.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L714-L725
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L714-L725

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z_34_implies_not_A {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) → ¬ (Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) := by sorry
