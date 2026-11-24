-- Prove2me | Theorems.Thm_MomentComparison_cubeAverage_mul_const
-- name    : MomentComparison.cubeAverage_mul_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:29:44.519942+00:00
-- url     : https://prove2.me/theorems/518039d9-f8dc-420d-8c5b-64fcd629c7fe
-- title:
--   Moment Comparison: cube Average mul const
-- statement:
--   The Moment Comparison construction uses the cube Average mul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean#L57-L59
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean#L57-L59

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset

theorem MomentComparison.cubeAverage_mul_const {n : ℕ} (f : Cube n → ℝ) (c : ℝ) :
    cubeAverage (fun x => f x * c) = cubeAverage f * c := by sorry
