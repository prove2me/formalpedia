-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_discardedStep_eq_boundary_sub
-- name    : Lean4LPD.PauliString.discardedStep_eq_boundary_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:39.861401+00:00
-- url     : https://prove2.me/theorems/a2ce0374-2afd-48f7-9375-9d962744a25f
-- title:
--   Pauli String: discarded Step eq boundary sub
-- statement:
--   `X_{d+1}` is the operator after the last rotation of the block and before the cut, minus
--   the scheduled trajectory at the boundary (`apd:eq:step_component`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L220-L228
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L220-L228

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

theorem Lean4LPD.PauliString.discardedStep_eq_boundary_sub (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    discardedStep Gs θ period wstar O d =
      rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1))) -
      trotterTraj Gs θ period wstar O ((d + 1) * period) := by sorry
