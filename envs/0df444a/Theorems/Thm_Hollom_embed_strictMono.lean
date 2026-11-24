-- Prove2me | Theorems.Thm_Hollom_embed_strictMono
-- name    : Hollom.embed_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:10:16.391013+00:00
-- url     : https://prove2.me/theorems/98e2c7d4-3603-4b46-98be-657617f3f7a4
-- title:
--   Hollom: embed strict Mono
-- statement:
--   The Hollom construction uses the embed strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L214-L214
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L214-L214

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

theorem Hollom.embed_strictMono {n : ℕ} : StrictMono (embed n) := by sorry
