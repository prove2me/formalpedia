-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_trotterStep_error_le
-- name    : Lean4LPD.PauliString.pauliNorm_trotterStep_error_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:10.070672+00:00
-- url     : https://prove2.me/theorems/872eb0d6-c926-4a47-88df-7205a1863a38
-- title:
--   Pauli String: pauli Norm trotter Step error le
-- statement:
--   **The truncation error is bounded at Pauli-norm level.** The operator telescope of
--   `apd:thm:triangle`, Minkowski's inequality and invariance of the Pauli norm bound the error by
--   the sum of the Pauli norms of the discarded operators `X_{d+1}` (`apd:eq:step_component`).
--   This is the norm-level part of `apd:thm:triangle`; the passage to expectation values in a
--   state is not formalized.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L216-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L216-L223

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

theorem Lean4LPD.PauliString.pauliNorm_trotterStep_error_le {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((blockEnd Gs θ period) ^ r) O - trotterStepTraj Gs θ period wstar O r) ≤
      ∑ d ∈ range r, pauliNorm (discardedStep Gs θ period wstar O d) := by sorry
