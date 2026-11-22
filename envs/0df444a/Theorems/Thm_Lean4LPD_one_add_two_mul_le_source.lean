-- Prove2me | Theorems.Thm_Lean4LPD_one_add_two_mul_le_source
-- name    : Lean4LPD.one_add_two_mul_le_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:37.543438+00:00
-- url     : https://prove2.me/theorems/33ed2b9f-aaaa-46a6-ae49-cf24b98a1727
-- title:
--   Lean4 LPD: one add two mul le source
-- statement:
--   Comparison with the paper's constant: `1 + 2β ≤ 1 + 4eβ`, since `2 ≤ 4e`. Stated as a lemma
--   so that the sharpening in `entryFactor_le` is a checked comparison rather than prose only.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L298-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L298-L303

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.one_add_two_mul_le_source {b : ℝ} (hb : 0 ≤ b) :
    1 + 2 * b ≤ 1 + 4 * Real.exp 1 * b := by sorry
