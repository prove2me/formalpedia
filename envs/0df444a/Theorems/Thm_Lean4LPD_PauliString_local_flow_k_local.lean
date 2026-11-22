-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_local_flow_k_local
-- name    : Lean4LPD.PauliString.local_flow_k_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:34.666139+00:00
-- url     : https://prove2.me/theorems/f384e757-6901-40d4-8957-9d1e2c254d52
-- title:
--   Pauli String: local flow k local
-- statement:
--   **`apd:thm:local_flow_k_local`, in the paper's variables.**
--
--   For a Hermitian `k_h`-local generator and a rung `m ≥ 2`, the high-weight norm above
--   `w_m = k_o + (m-1)(k_h-1)` grows by at most `|sin(dt)|` times the norm above
--   `w_{m-1}`. Rung `1` needs `highNorm_conj_le_pauliNorm` instead, which bounds the inflow by the
--   total mass; rung `0` is the reservoir, not a weight.
--
--   The inequality holds for every operator `O` and every angle `θ`: no locality hypothesis on the
--   observable is used, which is stronger than the paper's statement. Here `k_o` only fixes the
--   rung weights.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Flow.lean#L702-L710
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Flow.lean#L702-L710

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ} {G : PauliString n} {p : PauliIndex n} {kh w w' : ℕ}

theorem Lean4LPD.PauliString.local_flow_k_local {ko m : ℕ} (hG : IsSelfAdjoint G) (hk : weight G ≤ kh) (hm : 2 ≤ m)
    (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm (rungWeight ko kh m) (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm (rungWeight ko kh m) O
        + |Real.sin θ| * highNorm (rungWeight ko kh (m - 1)) O := by sorry
