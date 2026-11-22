-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterStep_telescoping
-- name    : Lean4LPD.PauliString.trotterStep_telescoping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:41:47.155498+00:00
-- url     : https://prove2.me/theorems/25ed9ca2-d267-4e51-a0d4-df51b4ea029f
-- title:
--   Pauli String: trotter Step telescoping
-- statement:
--   **The operator telescope.** The identity of `apd:thm:triangle`: the untruncated evolution
--   minus the LPD output after `r` steps is the sum of the discarded operators, each evolved through
--   the remaining whole steps. Here `discardedStep d` is the zero-based `X_{d+1}` of
--   `apd:eq:step_component`; its description as a high-weight projection is
--   `discardedStep_eq_truncOp`. The proof is an induction on `r` that unfolds the definition of
--   `discardedStep`; it needs no Hermiticity, locality or angle hypothesis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L135-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L135-L158

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

theorem Lean4LPD.PauliString.trotterStep_telescoping (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    ((blockEnd Gs θ period) ^ r) O - trotterStepTraj Gs θ period wstar O r =
      ∑ d ∈ range r, ((blockEnd Gs θ period) ^ (r - 1 - d))
        (discardedStep Gs θ period wstar O d) := by sorry
