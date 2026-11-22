-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sum_norm_coeff_sq
-- name    : Lean4LPD.PauliString.sum_norm_coeff_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:49.436066+00:00
-- url     : https://prove2.me/theorems/6dff729c-105b-4677-8384-275fbba81a0a
-- title:
--   Pauli String: sum norm coeff sq
-- statement:
--   **Parseval: `‖O‖_{2,normalized} = ‖x‖_{ℓ²}`, squared.** This is the identity the proof of
--   `apd:thm:local_flow_k_local` starts from; it expresses the orthonormality of the Pauli strings for
--   `⟨A,B⟩ = 2^{-n} Tr(A† B)`.
--
--   Proved directly from the character sum rather than through an orthonormal basis, so it does
--   **not** by itself give the expansion `O = ∑_P x_P P`; that is `sum_coeff_smul_toMatrix_herm` in
--   `Pauli/Truncate.lean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L301-L321
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L301-L321

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

theorem Lean4LPD.PauliString.sum_norm_coeff_sq (O : Matrix (Bits n) (Bits n) ℂ) :
    ∑ p : PauliIndex n, ‖coeff O p‖ ^ 2 = pauliNormSq O := by sorry
