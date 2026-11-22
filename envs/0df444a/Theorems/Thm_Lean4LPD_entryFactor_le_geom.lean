-- Prove2me | Theorems.Thm_Lean4LPD_entryFactor_le_geom
-- name    : Lean4LPD.entryFactor_le_geom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:24.543185+00:00
-- url     : https://prove2.me/theorems/8b86a7a2-b1b0-47de-a289-3eb1c54f895d
-- title:
--   Lean4 LPD: entry Factor le geom
-- statement:
--   **The entry-factor bound, geometric form.** For every `β < 1`,
--
--     `E_ν ≤ ε_ν^{(ν)} / (1 − β)`.
--
--   No `β ≤ 1/2` is needed; that hypothesis enters only in converting to the affine form
--   `entryFactor_le`. The proof sums the geometric majorant supplied by `epsJump_ratio`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L228-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L228-L265

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.entryFactor_le_geom {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {nu : ℕ} (hnu : 1 ≤ nu) (hb1 : betaOf kh1 c a < 1) :
    entryFactor kh1 c a nu ≤ epsJump kh1 c a nu nu / (1 - betaOf kh1 c a) := by sorry
