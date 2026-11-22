-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
-- name    : Lean4LPD.PauliString.support_phaseMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:36.22791+00:00
-- url     : https://prove2.me/theorems/7d579855-e0d5-4399-86c8-140e0447b2e5
-- title:
--   Pauli String: support phase Mul
-- statement:
--   The support does not see the phase — the `Finset` refinement of `weight_phaseMul`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L110-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L110-L111

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.support_phaseMul (k : ZMod 4) (s : PauliString n) :
    support (phaseMul k s) = support s := by sorry

attribute [defeq] Lean4LPD.PauliString.support_phaseMul
