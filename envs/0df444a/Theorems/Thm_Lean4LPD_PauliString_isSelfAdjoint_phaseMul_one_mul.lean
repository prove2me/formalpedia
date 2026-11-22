-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_phaseMul_one_mul
-- name    : Lean4LPD.PauliString.isSelfAdjoint_phaseMul_one_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:26.921962+00:00
-- url     : https://prove2.me/theorems/d5843a98-67a7-48da-8815-a48269d9fb49
-- title:
--   Pauli String: is Self Adjoint phase Mul one mul
-- statement:
--   **The partner Pauli `i G s` is again Hermitian**, for Hermitian `G` and `s` with
--   `⟪G,s⟫ = 1`. Together with `sympForm_mul_self_right` this is the property of the partner
--   `s' = ±i G s` used in the proof of `apd:thm:local_flow_k_local`.
--
--   It is needed for the anticommuting branch to mean anything physically:
--   `cos(dt) s + i sin(dt) G s` is an observable only if `i G s` is. Note the Hermitian Pauli strings
--   are *not* closed under multiplication — `G s` itself is anti-Hermitian when `G` and `s`
--   anticommute, which is exactly why the partner carries the factor `i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L434-L443
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L434-L443

module
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}

theorem Lean4LPD.PauliString.isSelfAdjoint_phaseMul_one_mul {G s : PauliString n} (hG : IsSelfAdjoint G)
    (hs : IsSelfAdjoint s) (h : sympForm G s = 1) : IsSelfAdjoint (phaseMul 1 (G * s)) := by sorry
