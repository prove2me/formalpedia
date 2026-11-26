-- Prove2me | Theorems.Thm_N4Code_pickSubset_subset
-- name    : N4Code.pickSubset_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:15.66163+00:00
-- url     : https://prove2.me/theorems/c5701406-774a-4a5d-b023-b417103fc53c
-- title:
--   N4 Code: pick Subset subset
-- statement:
--   The picked subset is contained in s.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1108-L1110
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1108-L1110

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.pickSubset_subset {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    pickSubset s k hk ⊆ s := by sorry
