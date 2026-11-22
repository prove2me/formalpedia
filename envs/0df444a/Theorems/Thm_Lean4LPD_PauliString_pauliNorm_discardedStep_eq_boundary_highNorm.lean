-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_discardedStep_eq_boundary_highNorm
-- name    : Lean4LPD.PauliString.pauliNorm_discardedStep_eq_boundary_highNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:30.92278+00:00
-- url     : https://prove2.me/theorems/92fdd9bc-c670-458a-9d29-4cf883778591
-- title:
--   Pauli String: pauli Norm discarded Step eq boundary high Norm
-- statement:
--   At a Trotter boundary, the Pauli norm of the discarded operator is the high-weight norm of
--   the last rotation applied to the scheduled trajectory, which is the quantity that the local-flow
--   bound controls (`apd:thm:triangle`). No such identification is made at interior rotations, where
--   nothing is discarded.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L234-L240
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L234-L240

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

theorem Lean4LPD.PauliString.pauliNorm_discardedStep_eq_boundary_highNorm (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) (hp : 0 < period) :
    pauliNorm (discardedStep Gs θ period wstar O d) = highNorm wstar
      (rot (toMatrix (Gs (period - 1))) (θ (period - 1)) *
        trotterTraj Gs θ period wstar O (d * period + (period - 1)) *
        rot (toMatrix (Gs (period - 1))) (-(θ (period - 1)))) := by sorry
