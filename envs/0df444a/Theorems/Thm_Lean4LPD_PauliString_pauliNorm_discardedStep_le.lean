-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_discardedStep_le
-- name    : Lean4LPD.PauliString.pauliNorm_discardedStep_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:42:52.908924+00:00
-- url     : https://prove2.me/theorems/c28e0b55-373f-4ca2-bce0-bbb8f1b07f7b
-- title:
--   Pauli String: pauli Norm discarded Step le
-- statement:
--   The single-rotation flow bound `highNorm_conj_trajTrunc_le`, applied to the last rotation
--   of a step, bounds the discarded operator `X_{d+1}`
--   (`apd:eq:step_component`; `apd:thm:local_flow_k_local`). This is a one-rotation estimate: its
--   right-hand side still contains the two ladder rungs of the trajectory just before the boundary.
--   The multi-layer bound on the sum of the discarded norms is in `LayerError.lean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L247-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L247-L269

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

theorem Lean4LPD.PauliString.pauliNorm_discardedStep_le {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {period wstar ko kh m : ℕ} {O : Matrix (Bits n) (Bits n) ℂ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (hp : 0 < period) (hm : 1 ≤ m) (hcut : wstar = rungWeight ko kh m) (d : ℕ) :
    let g := d * period + (period - 1)
    pauliNorm (discardedStep Gs θ period wstar O d) ≤
      ladderNTrunc (fun j => Gs (j % period)) (fun j => θ (j % period))
          (trotterSchedule period wstar) O ko kh m g +
        |Real.sin (θ (period - 1))| *
          ladderNTrunc (fun j => Gs (j % period)) (fun j => θ (j % period))
            (trotterSchedule period wstar) O ko kh (m - 1) g := by sorry
