-- Prove2me | Theorems.Thm_N4Code_equivalent_trans
-- name    : N4Code.equivalent_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:25:16.731801+00:00
-- url     : https://prove2.me/theorems/38f7cd23-554a-5718-88ea-0b45e26ead28
-- title:
--   N4 Code: equivalent trans
-- statement:
--   Equivalence is transitive.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2358-L2368
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2358-L2368

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.equivalent_trans {n : ℕ} {C₁ C₂ C₃ : Code n} (h12 : Equivalent C₁ C₂)
    (h23 : Equivalent C₂ C₃) : Equivalent C₁ C₃ := by sorry
