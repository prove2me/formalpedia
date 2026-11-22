-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_discardedStep
-- name    : Lean4LPD.PauliString.pauliNorm_discardedStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:35:59.120851+00:00
-- url     : https://prove2.me/theorems/09188983-3582-4a95-919d-000dc421508e
-- title:
--   Pauli String: pauli Norm discarded Step
-- statement:
--   The discarded operator's Pauli norm is the pre-truncation high-weight mass
--   (`apd:thm:triangle`; `apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L190-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L190-L194

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.pauliNorm_discardedStep (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    pauliNorm (discardedStep Gs θ period wstar O d) =
      highNorm wstar (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by sorry
