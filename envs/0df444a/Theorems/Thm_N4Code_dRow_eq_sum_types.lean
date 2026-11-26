-- Prove2me | Theorems.Thm_N4Code_dRow_eq_sum_types
-- name    : N4Code.dRow_eq_sum_types
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:44.382521+00:00
-- url     : https://prove2.me/theorems/ef86566f-52e1-5a24-a4dc-b1756bb994d5
-- title:
--   N4 Code: d Row eq sum types
-- statement:
--   d_j(y) from the types in S only, when all columns are of types in S.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L618-L631
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L618-L631

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRow_eq_sum_types {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) (S : Finset ℕ)
    (hSle : S ⊆ Finset.Icc 0 15) (hS : ∀ t : Fin n, colVal (C t) ∈ S) :
    dRow C j y = ∑ i ∈ S, if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by sorry
