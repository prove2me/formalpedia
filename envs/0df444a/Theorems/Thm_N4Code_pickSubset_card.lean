-- Prove2me | Theorems.Thm_N4Code_pickSubset_card
-- name    : N4Code.pickSubset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:17.880039+00:00
-- url     : https://prove2.me/theorems/7678c1dc-b968-455d-a994-025bd14d69f0
-- title:
--   N4 Code: pick Subset card
-- statement:
--   The picked subset has cardinality k.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1113-L1115
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1113-L1115

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.pickSubset_card {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    (pickSubset s k hk).card = k := by sorry
