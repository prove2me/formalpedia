-- Prove2me | Theorems.Thm_Lean4LPD_epsJump_ratio
-- name    : Lean4LPD.epsJump_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:49.526966+00:00
-- url     : https://prove2.me/theorems/f3af7679-c9ea-42d3-82c5-672b4e206472
-- title:
--   Lean4 LPD: eps Jump ratio
-- statement:
--   **The term-ratio bound**: for `j ≥ ν ≥ 1`,
--
--     `ε_{j+1}^{(ν)} ≤ β · ε_j^{(ν)}`.
--
--   This geometric decay of the terms is what drives `entryFactor_le_geom`. Two estimates, both
--   termwise: `w_{ν+j+1} ≤ w_{ν+j}·(1 + 1/j)` because `ν+j−1+c ≥ j`, and
--   `w_{ν+j+1} ≤ w₂·(ν+j) ≤ 2w₂·j` because `ν ≤ j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L123-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean#L123-L214

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.epsJump_ratio {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {j nu : ℕ} (hnu : 1 ≤ nu) (hj : nu ≤ j) :
    epsJump kh1 c a (j + 1) nu ≤ betaOf kh1 c a * epsJump kh1 c a j nu := by sorry
