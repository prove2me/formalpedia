-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_card_lowSet_le_pow
-- name    : Lean4LPD.PauliString.card_lowSet_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:25.465173+00:00
-- url     : https://prove2.me/theorems/fc025a07-6ecb-4cc9-943c-dc4b176d711c
-- title:
--   Pauli String: card low Set le pow
-- statement:
--   The same bound as a polynomial in `n`: `C(n,w) ≤ n^w`. This is the form
--   `apd:thm:runtime`'s `O(n^{w*})` names.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Count.lean#L149-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Count.lean#L149-L153

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Count
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.card_lowSet_le_pow (n w : ℕ) (hw : w ≤ n) :
    (lowSet n w).card ≤ 4 ^ w * n ^ w := by sorry
