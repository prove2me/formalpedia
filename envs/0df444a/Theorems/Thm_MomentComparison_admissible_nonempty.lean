-- Prove2me | Theorems.Thm_MomentComparison_admissible_nonempty
-- name    : MomentComparison.admissible_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:59:07.868804+00:00
-- url     : https://prove2.me/theorems/aaa3d3bc-a9e6-4434-870d-d3be7b92d494
-- title:
--   Moment Comparison: admissible nonempty
-- statement:
--   The set whose infimum defines `Cstar` is nonempty.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/RealHypercontractivity.lean#L195-L199
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/RealHypercontractivity.lean#L195-L199

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_RealHypercontractivity
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison

theorem MomentComparison.admissible_nonempty :
    {C : ℝ | 0 < C ∧ ∀ (n d : ℕ), 0 < n → 0 < d → ∀ f : Cube n → ℝ,
      HasDegreeLE f d →
        Real.sqrt (cubeAverage fun x => f x ^ 2) ≤ C ^ d * cubeAverage (fun x => |f x|)}.Nonempty := by sorry
