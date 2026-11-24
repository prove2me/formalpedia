-- Prove2me | Theorems.Thm_MomentComparison_hasDegreeLE_sum_walsh
-- name    : MomentComparison.hasDegreeLE_sum_walsh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:29:43.571397+00:00
-- url     : https://prove2.me/theorems/a3a8e1d1-7ab3-43ee-95a0-a758f44806d6
-- title:
--   Moment Comparison: has Degree LE sum walsh
-- statement:
--   The Moment Comparison construction uses the has Degree LE sum walsh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean#L122-L133
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean#L122-L133

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

theorem MomentComparison.hasDegreeLE_sum_walsh {n d : ℕ} {ι : Type*} (u : Finset ι)
    (s : ι → Finset (Fin n)) (a : ι → ℝ)
    (h : ∀ i ∈ u, (s i).card ≤ d) :
    HasDegreeLE (fun x => ∑ i ∈ u, a i * walsh (s i) x) d := by sorry
