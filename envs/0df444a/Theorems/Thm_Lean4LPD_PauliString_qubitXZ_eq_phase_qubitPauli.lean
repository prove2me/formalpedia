-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_qubitXZ_eq_phase_qubitPauli
-- name    : Lean4LPD.PauliString.qubitXZ_eq_phase_qubitPauli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:05.665347+00:00
-- url     : https://prove2.me/theorems/94dda367-51f0-46cd-8c96-3cd86a9f49ff
-- title:
--   Pauli String: qubit XZ eq phase qubit Pauli
-- statement:
--   The one-qubit phase correction: `X^x Z^z` is `i ^ (-(x z))` times the positive Pauli
--   matrix of `def:pauli_basis`. Only the `Y` site `x = z = 1` carries a nontrivial phase.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L76-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Tensor.lean#L76-L114

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Tensor
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Matrix Finset

theorem Lean4LPD.PauliString.qubitXZ_eq_phase_qubitPauli (x z : ZMod 2) :
    qubitXZ x z = iPow (-((x * z).val : ZMod 4)) • qubitPauli x z := by sorry
