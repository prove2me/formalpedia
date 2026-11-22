-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sub_truncOp
-- name    : Lean4LPD.PauliString.sub_truncOp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:52.84045+00:00
-- url     : https://prove2.me/theorems/9fff9e3c-f5e2-4955-ae6a-4820cbeb569d
-- title:
--   Pauli String: sub trunc Op
-- statement:
--   **The discarded operator is the complementary projection.** This generalizes the
--   `1 - Π_{≤ w*}` in `apd:eq:step_component` to any retained set `S`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L80-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Discard.lean#L80-L85

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

theorem Lean4LPD.PauliString.sub_truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    O - truncOp S O = truncOp Sᶜ O := by sorry
