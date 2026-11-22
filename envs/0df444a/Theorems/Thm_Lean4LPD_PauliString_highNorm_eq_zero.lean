-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_highNorm_eq_zero
-- name    : Lean4LPD.PauliString.highNorm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:47.088799+00:00
-- url     : https://prove2.me/theorems/d3e3eabb-5caa-46b2-8d48-f3851bcc780e
-- title:
--   Pauli String: high Norm eq zero
-- statement:
--   A `k_o`-local observable has no mass above weight `k_o`: `init` for the ladder. Locality is
--   read through the coefficient vector (cf. `def:support`): every class carrying a non-zero
--   coefficient has weight at most `w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L451-L458
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L451-L458

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.highNorm_eq_zero (w : ℕ) {O : Matrix (Bits n) (Bits n) ℂ}
    (h : ∀ p : PauliIndex n, w < wt p → coeff O p = 0) : highNorm w O = 0 := by sorry
