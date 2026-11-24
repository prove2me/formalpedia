-- Prove2me | Theorems.Thm_MomentComparison_cubeAverage_walsh_mul
-- name    : MomentComparison.cubeAverage_walsh_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:17:31.042837+00:00
-- url     : https://prove2.me/theorems/19c499ac-2593-49de-8b7d-87cbea5f6881
-- title:
--   Moment Comparison: cube Average walsh mul
-- statement:
--   The Moment Comparison construction uses the cube Average walsh mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean#L117-L120
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean#L117-L120

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

theorem MomentComparison.cubeAverage_walsh_mul {n : ℕ} (s t : Finset (Fin n)) :
    cubeAverage (fun x => walsh s x * walsh t x) = if s = t then 1 else 0 := by sorry
