-- Prove2me | Theorems.Thm_Lean4LPD_partFactor_le_of_one_le
-- name    : Lean4LPD.partFactor_le_of_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:55.975484+00:00
-- url     : https://prove2.me/theorems/fd552e2e-e05f-4cb9-81f1-67913b313024
-- title:
--   Lean4 LPD: part Factor le of one le
-- statement:
--   The part-factor estimate including single jumps. The `j≥2` part is `partFactor_le`;
--   the `j=1` part is exact. Supporting theorem for `apd:eq:part_factor`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L141-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/ChainWeights.lean#L141-L147

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.partFactor_le_of_one_le {j : ℕ} {s : ℝ} (hj : 1 ≤ j) (hs : (j : ℝ) ≤ s) :
    partFactor j s ≤ (9 / 4 : ℝ) ^ (j - 1) := by sorry
