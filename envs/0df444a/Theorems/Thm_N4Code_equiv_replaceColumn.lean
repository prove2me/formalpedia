-- Prove2me | Theorems.Thm_N4Code_equiv_replaceColumn
-- name    : N4Code.equiv_replaceColumn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:03.396923+00:00
-- url     : https://prove2.me/theorems/8b001fbf-79cc-549b-9b8e-87d4ea9ac05a
-- title:
--   N4 Code: equiv replace Column
-- statement:
--   Replacing a column commutes with code equivalence: the modified column at
--   the corresponding position is the transformed s'.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L942-L956
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L942-L956

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.equiv_replaceColumn {n : ℕ} {C C0 : Code n} (h : Equivalent C C0) (t : Fin n)
    (s' : Column) :
    ∃ t' : Fin n, ∃ s'' : Column,
      Equivalent (replaceColumn C t s') (replaceColumn C0 t' s'') := by sorry
