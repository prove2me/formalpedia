-- Prove2me | Theorems.Thm_Lean4LPD_chainWeight_zero
-- name    : Lean4LPD.chainWeight_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:31.823098+00:00
-- url     : https://prove2.me/theorems/95f8a59b-e2a9-4f06-b0f3-19307939f048
-- title:
--   Lean4 LPD: chain Weight zero
-- statement:
--   The empty all-ones chain has weight one, as required for the reservoir entry in
--   `apd:eq:composition_majorant`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L57-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L57-L58

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.chainWeight_zero (kh1 c a : ℝ) : chainWeight kh1 c a 0 = 1 := by sorry
