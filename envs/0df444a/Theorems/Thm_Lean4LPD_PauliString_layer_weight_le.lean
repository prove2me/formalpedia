-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layer_weight_le
-- name    : Lean4LPD.PauliString.layer_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:50.905183+00:00
-- url     : https://prove2.me/theorems/8786ea08-809f-4321-aec6-05f3318207d1
-- title:
--   Pauli String: layer weight le
-- statement:
--   **One layer multiplies the Pauli weight by at most `k_h`.** This is the per-layer step in the
--   proof of `apd:thm:lightcone`, obtained by combining the containment `support_subset_cover` with
--   the count `card_cover_le`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L400-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L400-L402

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.layer_weight_le (hL : IsLayer kh L) (hkh : 1 ≤ kh) (hq : q ∈ oneLayer L p) :
    weight q ≤ kh * weight p := by sorry
