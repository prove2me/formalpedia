-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_highNorm_le_pauliNorm
-- name    : Lean4LPD.PauliString.highNorm_le_pauliNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:20.284064+00:00
-- url     : https://prove2.me/theorems/2d88b7a5-3b65-44e3-9545-29ded7e8b3d4
-- title:
--   Pauli String: high Norm le pauli Norm
-- statement:
--   The high-weight mass never exceeds the total mass: `‖O_{≥ w+1}‖_{2,normalized} ≤
--   ‖O‖_{2,normalized}` at every
--   threshold `w`. This is the inequality behind the base case of the induction in
--   `apd:cor:norm_cumulation_jump`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L443-L446
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L443-L446

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

theorem Lean4LPD.PauliString.highNorm_le_pauliNorm (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w O ≤ pauliNorm O := by sorry
