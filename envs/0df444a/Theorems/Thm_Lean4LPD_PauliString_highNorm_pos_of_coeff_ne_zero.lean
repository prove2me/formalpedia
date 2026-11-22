-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_highNorm_pos_of_coeff_ne_zero
-- name    : Lean4LPD.PauliString.highNorm_pos_of_coeff_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:19.444876+00:00
-- url     : https://prove2.me/theorems/b6d2ce1b-9c8f-44eb-bac1-c4ce03e28dab
-- title:
--   Pauli String: high Norm pos of coeff ne zero
-- statement:
--   The converse of `highNorm_eq_zero`: a single nonzero coefficient above the cut forces
--   positive high-weight mass. Used wherever a witness must show the discarded sector is really
--   occupied rather than merely reachable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L463-L468
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L463-L468

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.highNorm_pos_of_coeff_ne_zero {w : ℕ} {O : Matrix (Bits n) (Bits n) ℂ}
    {p : PauliIndex n} (hp : w < wt p) (h : coeff O p ≠ 0) : 0 < highNorm w O := by sorry
