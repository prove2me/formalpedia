-- Prove2me | Theorems.Thm_Hollom_mapsTo_Icc_image
-- name    : Hollom.mapsTo_Icc_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:57.861018+00:00
-- url     : https://prove2.me/theorems/dc748743-6b52-4a29-bb8c-bf9ff5336911
-- title:
--   Hollom: maps To Icc image
-- statement:
--   The Hollom construction uses the maps To Icc image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L629-L635
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L629-L635

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
import Definitions.Def_AharoniKorman_Counterexample
set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
variable {f : SpinalMap C}
open Finset

theorem Hollom.mapsTo_Icc_image (hC : IsChain (· ≤ ·) C) {a b c d n : ℕ}
    (hab : h(a, b, n) ∈ C) (hcd : h(c, d, n) ∈ C) :
    Set.MapsTo f
      ((Icc (a, b) (c, d)).image (embed n))
      ((Icc (a, b) (c, d)).image (embed n)) := by sorry
