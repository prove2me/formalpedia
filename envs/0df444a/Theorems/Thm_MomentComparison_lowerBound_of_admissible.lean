-- Prove2me | Theorems.Thm_MomentComparison_lowerBound_of_admissible
-- name    : MomentComparison.lowerBound_of_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:59:09.693585+00:00
-- url     : https://prove2.me/theorems/b1a41df0-00d6-4fe1-8ded-603440b81a2b
-- title:
--   Moment Comparison: lower Bound of admissible
-- statement:
--   Every admissible base is at least √3, as witnessed by squares of symmetric Walsh sums.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Lower.lean#L174-L194
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Lower.lean#L174-L194

module
public import Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_FiniteFourth
public import Definitions.Def_MomentComparison_RealHypercontractivity
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Lower
set_option autoImplicit true
@[expose] public section
public section
open Filter Finset
open scoped Topology
open MomentComparison

theorem MomentComparison.lowerBound_of_admissible {C : ℝ} (hC : 0 < C)
    (h : ∀ (n d : ℕ), 0 < n → 0 < d → ∀ f : Cube n → ℝ, HasDegreeLE f d →
      Real.sqrt (cubeAverage fun x => f x ^ 2) ≤ C ^ d * cubeAverage (fun x => |f x|)) :
    Real.sqrt 3 ≤ C := by sorry
