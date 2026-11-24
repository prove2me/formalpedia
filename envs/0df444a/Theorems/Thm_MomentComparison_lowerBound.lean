-- Prove2me | Theorems.Thm_MomentComparison_lowerBound
-- name    : MomentComparison.lowerBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:03:34.349038+00:00
-- url     : https://prove2.me/theorems/ba94b4cf-c597-4da9-bbfc-4469158d0c77
-- title:
--   Moment Comparison: lower Bound
-- statement:
--   The lower bound in Theorem 2.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Lower.lean#L197-L201
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Lower.lean#L197-L201

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

theorem MomentComparison.lowerBound : Real.sqrt 3 ≤ Cstar := by sorry
