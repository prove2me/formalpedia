-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sub_truncOp_compl
-- name    : Lean4LPD.PauliString.sub_truncOp_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:13.678511+00:00
-- url     : https://prove2.me/theorems/203c4cc6-fef4-4a3e-b919-ea54d4389314
-- title:
--   Pauli String: sub trunc Op compl
-- statement:
--   The complementary retained set discards exactly the `S` component; at `S = highSet n w*`
--   this is the operator identity in `apd:eq:step_component`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L89-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L89-L91

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.sub_truncOp_compl (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    O - truncOp Sᶜ O = truncOp S O := by sorry
