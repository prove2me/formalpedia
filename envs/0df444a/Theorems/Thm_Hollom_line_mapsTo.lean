-- Prove2me | Theorems.Thm_Hollom_line_mapsTo
-- name    : Hollom.line_mapsTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:09:21.620845+00:00
-- url     : https://prove2.me/theorems/299090a6-0cf9-4bd7-8c97-cdd310a85847
-- title:
--   Hollom: line maps To
-- statement:
--   The Hollom construction uses the line maps To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L276-L286
-- source:
--   https://github.com/b-mehta/AharoniKorman/blob/ea16ed47faa49d6d815c8fb397b02e71b231781b/AharoniKorman/Counterexample.lean#L276-L286

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

theorem Hollom.line_mapsTo {x y : Hollom} (hxy : (ofHollom x).2.2 = (ofHollom y).2.2) :
    Set.MapsTo line (Set.Icc x y) (Set.Icc (line x) (line y)) := by sorry
