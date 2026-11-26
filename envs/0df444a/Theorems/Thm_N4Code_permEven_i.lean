-- Prove2me | Theorems.Thm_N4Code_permEven_i
-- name    : N4Code.permEven_i
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:02.888575+00:00
-- url     : https://prove2.me/theorems/74175eb4-0694-49f7-93dc-99772a11cb6f
-- title:
--   N4 Code: perm Even i
-- statement:
--   The N4 Code construction uses the perm Even i property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1974-L2000
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1974-L2000

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.permEven_i (i j : Fin 4) (hij : i ≠ j) : permEven i j i = (0 : Fin 4) := by sorry
