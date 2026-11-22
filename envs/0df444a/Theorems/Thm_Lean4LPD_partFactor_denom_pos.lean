-- Prove2me | Theorems.Thm_Lean4LPD_partFactor_denom_pos
-- name    : Lean4LPD.partFactor_denom_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:47.617661+00:00
-- url     : https://prove2.me/theorems/9e2a7799-f260-4ad2-bf6b-1d26a09217f0
-- title:
--   Lean4 LPD: part Factor denom pos
-- statement:
--   The Lean4 LPD construction uses the part Factor denom pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L69-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean#L69-L73

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.partFactor_denom_pos {j : ℕ} {s : ℝ} (hs : (j : ℝ) ≤ s) :
    0 < ∏ i ∈ range j, (s - j + 1 + i) := by sorry
