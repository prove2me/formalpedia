-- Prove2me | Theorems.Thm_MomentComparison_walsh_kernel
-- name    : MomentComparison.walsh_kernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:37:16.232831+00:00
-- url     : https://prove2.me/theorems/cc27772c-12d1-4903-be3a-9b74da24d9a3
-- title:
--   Moment Comparison: walsh kernel
-- statement:
--   The Walsh kernel is diagonal in the point basis of the cube.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean#L165-L180
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Walsh.lean#L165-L180

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

theorem MomentComparison.walsh_kernel {n : ℕ} (x y : Cube n) :
    (∑ s : Finset (Fin n), walsh s x * walsh s y) = if x = y then (2 : ℝ)^n else 0 := by sorry
