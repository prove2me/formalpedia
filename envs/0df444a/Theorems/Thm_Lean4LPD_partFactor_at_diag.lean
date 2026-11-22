-- Prove2me | Theorems.Thm_Lean4LPD_partFactor_at_diag
-- name    : Lean4LPD.partFactor_at_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:19.924463+00:00
-- url     : https://prove2.me/theorems/892a576b-482b-4e04-b199-0a034b72aac5
-- title:
--   Lean4 LPD: part Factor at diag
-- statement:
--   The maximum, at `s = j` (`σ = j`, `c = 0`): `ρ(j,j)|_{c=0} = (2j−1)^j/(j!)²`, which is
--   `diagFactor j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L120-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L120-L128

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.partFactor_at_diag (j : ℕ) : partFactor j (j : ℝ)
    = (2 * (j : ℝ) - 1) ^ j / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)) := by sorry
