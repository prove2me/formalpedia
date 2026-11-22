-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_discardedStep_eq_truncOp
-- name    : Lean4LPD.PauliString.discardedStep_eq_truncOp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:23.488808+00:00
-- url     : https://prove2.me/theorems/20642ab9-688d-488b-8cdb-b6312febb3f5
-- title:
--   Pauli String: discarded Step eq trunc Op
-- statement:
--   The discarded operator is the projection of the pre-truncation operator onto the Paulis of
--   weight above `wstar` (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L182-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L182-L186

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

theorem Lean4LPD.PauliString.discardedStep_eq_truncOp (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    discardedStep Gs θ period wstar O d = truncOp (highSet n wstar)
      (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period) := by sorry
