-- Prove2me | Theorems.Thm_MomentComparison_finite_fourth_ge
-- name    : MomentComparison.finite_fourth_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:40:15.757358+00:00
-- url     : https://prove2.me/theorems/76e3e913-f49a-4a99-a1af-4ca5480ae193
-- title:
--   Moment Comparison: finite fourth ge
-- statement:
--   The contribution of symmetric differences of size (2k) to the fourth moment.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/FiniteFourth.lean#L15-L37
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/FiniteFourth.lean#L15-L37

module
public import Definitions.Def_MomentComparison_Counting
public import Definitions.Def_MomentComparison_Walsh
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_FiniteFourth
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open MomentComparison

theorem MomentComparison.finite_fourth_ge (n m k : ℕ) (hkm : k ≤ m) :
    (n.choose (2 * k) : ℝ) * ((2 * k).choose k : ℝ) ^ 2 *
      ((n - 2 * k).choose (m - k) : ℝ) ^ 2 ≤
      cubeAverage (fun x => walshLayer n m x ^ 4) := by sorry
