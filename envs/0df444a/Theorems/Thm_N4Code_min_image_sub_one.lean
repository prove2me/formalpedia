-- Prove2me | Theorems.Thm_N4Code_min_image_sub_one
-- name    : N4Code.min_image_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:36.914128+00:00
-- url     : https://prove2.me/theorems/60623da6-f961-4342-9016-54ff53d94c2a
-- title:
--   N4 Code: min image sub one
-- statement:
--   The minimum over S of (f a − 1) is the minimum minus one.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L144-L161
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L144-L161

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.min_image_sub_one {α : Type*} {S : Finset α} {f : α → ℕ} (hS : S.Nonempty) :
    (S.image (fun a => f a - 1)).min' (hS.image (fun a => f a - 1)) =
      (S.image f).min' (hS.image f) - 1 := by sorry
