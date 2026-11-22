-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trotterTraj_succ
-- name    : Lean4LPD.PauliString.trotterTraj_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:36:49.586637+00:00
-- url     : https://prove2.me/theorems/56a6b244-d731-49cd-abf0-17e438bd5d08
-- title:
--   Pauli String: trotter Traj succ
-- statement:
--   One rotation of the boundary-scheduled execution (`apd:thm:triangle`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L94-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean#L94-L100

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

theorem Lean4LPD.PauliString.trotterTraj_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    trotterTraj Gs θ period wstar O (g + 1) =
      truncOp (trotterSchedule period wstar g)
        (rot (toMatrix (Gs (g % period))) (θ (g % period)) *
          trotterTraj Gs θ period wstar O g *
          rot (toMatrix (Gs (g % period))) (-(θ (g % period)))) := by sorry
