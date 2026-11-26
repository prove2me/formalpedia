-- Prove2me | Theorems.Thm_N4Code_rowPermute_xor
-- name    : N4Code.rowPermute_xor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:11.996833+00:00
-- url     : https://prove2.me/theorems/e96b34a8-9c75-46c7-ac0e-8fb79cbbc25c
-- title:
--   N4 Code: row Permute xor
-- statement:
--   Row-permutation algebra for composing two equivalences (the XOR flip).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2350-L2355
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2350-L2355

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.rowPermute_xor {ρ₁ ρ₂ : Equiv (Fin 4) (Fin 4)} (b₁ b₂ : Bool) (c : Column) :
    rowPermute ρ₂ (if b₂ = true then flipCol (rowPermute ρ₁ (if b₁ = true then flipCol c else c))
        else rowPermute ρ₁ (if b₁ = true then flipCol c else c)) =
      rowPermute (ρ₂.trans ρ₁) (if (b₁ != b₂) = true then flipCol c else c) := by sorry
