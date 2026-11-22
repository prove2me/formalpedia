-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_periodic_traj_error_le
-- name    : Lean4LPD.PauliString.pauliNorm_periodic_traj_error_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:50.170778+00:00
-- url     : https://prove2.me/theorems/8bb6fed8-03da-414e-ba64-3d18eaa53ce4
-- title:
--   Pauli String: pauli Norm periodic traj error le
-- statement:
--   The Pauli-norm triangle bound of `apd:thm:triangle` with the untruncated side written as
--   the rotation-indexed `traj` of the repeated block. The only hypothesis is Hermiticity of the
--   generators.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L228-L235
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L228-L235

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

theorem Lean4LPD.PauliString.pauliNorm_periodic_traj_error_le {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period wstar : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (traj (fun g => Gs (g % period)) (fun g => θ (g % period)) O (r * period) -
        trotterStepTraj Gs θ period wstar O r) ≤
      ∑ d ∈ range r, pauliNorm (discardedStep Gs θ period wstar O d) := by sorry
