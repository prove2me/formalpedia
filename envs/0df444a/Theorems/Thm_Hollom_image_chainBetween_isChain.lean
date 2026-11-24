-- Prove2me | Theorems.Thm_Hollom_image_chainBetween_isChain
-- name    : Hollom.image_chainBetween_isChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:54.522211+00:00
-- url     : https://prove2.me/theorems/62c5e58a-ecb6-4b14-aed4-da6e8331ac0e
-- title:
--   Hollom: image chain Between is Chain
-- statement:
--   The Hollom construction uses the image chain Between is Chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L598-L602
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L598-L602

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

theorem Hollom.image_chainBetween_isChain {a b c d n : ℕ} :
    IsChain (· ≤ ·) (((chainBetween a b c d).image (embed n)) : Set Hollom) := by sorry
