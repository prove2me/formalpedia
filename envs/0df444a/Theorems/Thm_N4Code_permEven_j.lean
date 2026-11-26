-- Prove2me | Theorems.Thm_N4Code_permEven_j
-- name    : N4Code.permEven_j
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:08.205266+00:00
-- url     : https://prove2.me/theorems/46e1b8a1-639d-459a-80ee-8a30e3e0e9e3
-- title:
--   N4 Code: perm Even j
-- statement:
--   The N4 Code construction uses the perm Even j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2002-L2007
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2002-L2007

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.permEven_j (i j : Fin 4) (_hij : i ≠ j) : permEven i j j = (1 : Fin 4) := by sorry
