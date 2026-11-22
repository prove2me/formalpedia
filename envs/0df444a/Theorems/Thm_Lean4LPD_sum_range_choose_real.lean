-- Prove2me | Theorems.Thm_Lean4LPD_sum_range_choose_real
-- name    : Lean4LPD.sum_range_choose_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:13.56482+00:00
-- url     : https://prove2.me/theorems/66c674ec-2714-4c30-bcc8-aba80e624a59
-- title:
--   Lean4 LPD: sum range choose real
-- statement:
--   Real-valued restatement, which is what the cumulation bound consumes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/HockeyStick.lean#L51-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/HockeyStick.lean#L51-L53

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.sum_range_choose_real (m g : ℕ) :
    ∑ l ∈ range g, (l.choose m : ℝ) = (g.choose (m + 1) : ℝ) := by sorry
