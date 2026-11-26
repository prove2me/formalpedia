-- Prove2me | Theorems.Thm_N4Code_C0form_iff_Columns07
-- name    : N4Code.C0form_iff_Columns07
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:46.772191+00:00
-- url     : https://prove2.me/theorems/fde232ec-ed86-43c8-bcd7-72014a18f17c
-- title:
--   N4 Code: C0form iff Columns07
-- statement:
--   In a Columns07 code, the C0 form means exactly types 1–4,7 are absent.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1512-L1562
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1512-L1562

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.C0form_iff_Columns07 {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    C0form C ↔ (count C 1 = 0 ∧ count C 2 = 0 ∧ count C 3 = 0 ∧ count C 4 = 0 ∧
      count C 7 = 0 ∧ Odd (count C 5) ∧ Odd (count C 6)) := by sorry
