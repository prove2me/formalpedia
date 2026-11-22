-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_trotterStep_error_le_highNorm
-- name    : Lean4LPD.PauliString.pauliNorm_trotterStep_error_le_highNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:47:10.18983+00:00
-- url     : https://prove2.me/theorems/11d384d4-bff4-410a-9a0a-6f3c8cfa4cef
-- title:
--   Pauli String: pauli Norm trotter Step error le high Norm
-- statement:
--   The norm-level triangle bound with the discarded norms written as the high-weight norms of
--   the operators before truncation, as in the last equality of `apd:thm:triangle`. These are not
--   the high-weight norms of the kept operators, which vanish.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L252-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L252-L259

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.pauliNorm_trotterStep_error_le_highNorm {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((blockEnd Gs θ period) ^ r) O - trotterStepTraj Gs θ period wstar O r) ≤
      ∑ d ∈ range r,
        highNorm wstar (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by sorry
