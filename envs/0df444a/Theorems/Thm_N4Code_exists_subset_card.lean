-- Prove2me | Theorems.Thm_N4Code_exists_subset_card
-- name    : N4Code.exists_subset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:11.176257+00:00
-- url     : https://prove2.me/theorems/837e027b-a4eb-5851-9b9e-2f0af9dd7899
-- title:
--   N4 Code: exists subset card
-- statement:
--   A subset of s of any size k ≤ s.card.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1066-L1069
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1066-L1069

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.exists_subset_card {α : Type*} [DecidableEq α] {s : Finset α} {k : ℕ}
    (hk : k ≤ s.card) : ∃ t : Finset α, t ⊆ s ∧ t.card = k := by sorry
