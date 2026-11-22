-- Prove2me | Theorems.Thm_Lean4LPD_prod_range_add_one_cast
-- name    : Lean4LPD.prod_range_add_one_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:48.00618+00:00
-- url     : https://prove2.me/theorems/d8c10b92-d816-4167-a4aa-0a7a26899375
-- title:
--   Lean4 LPD: prod range add one cast
-- statement:
--   `∏_{i<n} (i+1) = n!`, over `ℝ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L110-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L110-L116

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.prod_range_add_one_cast (n : ℕ) : ∏ i ∈ range n, ((i : ℝ) + 1) = (Nat.factorial n : ℝ) := by sorry
