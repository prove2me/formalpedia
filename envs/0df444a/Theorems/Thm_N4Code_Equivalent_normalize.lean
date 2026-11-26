-- Prove2me | Theorems.Thm_N4Code_Equivalent_normalize
-- name    : N4Code.Equivalent_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:12.033651+00:00
-- url     : https://prove2.me/theorems/197acfb5-7ca9-5cce-ba76-6ccc469c348f
-- title:
--   N4 Code: Equivalent normalize
-- statement:
--   The N4 Code construction uses the Equivalent normalize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2023-L2027
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2023-L2027

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.Equivalent_normalize {n : ℕ} (C : Code n) (i j : Fin 4) :
    Equivalent C (normalizeCode C i j) := by sorry
