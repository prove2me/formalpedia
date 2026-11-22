-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_trotterTraj_error_le
-- name    : Lean4LPD.PauliString.pauliNorm_trotterTraj_error_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:47:16.227877+00:00
-- url     : https://prove2.me/theorems/52188cc3-de52-47d9-a0c5-07b358d7e076
-- title:
--   Pauli String: pauli Norm trotter Traj error le
-- statement:
--   The norm-level error bound of `apd:thm:triangle` for the rotation-indexed execution
--   `trotterTraj` with cuts at step boundaries. Positive block length is needed only to identify
--   this scheduled trajectory with the step-indexed recurrence `trotterStepTraj`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L240-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L240-L247

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

theorem Lean4LPD.PauliString.pauliNorm_trotterTraj_error_le {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) (hp : 0 < period) :
    pauliNorm (traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) -
        trotterTraj Gs θ period wstar O (r * period)) ≤
      ∑ d ∈ range r, pauliNorm (discardedStep Gs θ period wstar O d) := by sorry
