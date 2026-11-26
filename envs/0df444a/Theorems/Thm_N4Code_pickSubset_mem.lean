-- Prove2me | Theorems.Thm_N4Code_pickSubset_mem
-- name    : N4Code.pickSubset_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:45.231809+00:00
-- url     : https://prove2.me/theorems/7a093124-0cc6-40ea-bcfb-596d729e1253
-- title:
--   N4 Code: pick Subset mem
-- statement:
--   The picked subset is a k-subset.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1103-L1105
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1103-L1105

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.pickSubset_mem {n : ℕ} {s : Finset (Fin n)} {k : ℕ} (hk : k ≤ s.card) :
    pickSubset s k hk ∈ s.powersetCard k := by sorry
