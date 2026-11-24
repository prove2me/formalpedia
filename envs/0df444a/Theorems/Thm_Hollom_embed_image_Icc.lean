-- Prove2me | Theorems.Thm_Hollom_embed_image_Icc
-- name    : Hollom.embed_image_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:08.025334+00:00
-- url     : https://prove2.me/theorems/ac125a03-3c37-4511-ab9f-80186355f786
-- title:
--   Hollom: embed image Icc
-- statement:
--   The Hollom construction uses the embed image Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L288-L292
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L288-L292

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

theorem Hollom.embed_image_Icc {a b c d n : ℕ} :
    embed n '' Set.Icc (a, b) (c, d) = Set.Icc h(a, b, n) h(c, d, n) := by sorry
