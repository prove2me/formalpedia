-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
-- name    : Lean4LPD.PauliString.sympForm_mul_self_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:57:59.453574+00:00
-- url     : https://prove2.me/theorems/e71732a1-5f13-4b05-a982-02ad26a56345
-- title:
--   Pauli String: symp Form mul self right
-- statement:
--   **The partner still anticommutes with the generator**: `⟪G, G s⟫ = ⟪G, s⟫`, by bilinearity
--   and `⟪G, G⟫ = 0`. The proof of `apd:thm:local_flow_k_local` pairs each Pauli `s` anticommuting
--   with the generator with a partner `s' = ±i G s` and uses that `s'` is again a Hermitian Pauli
--   anticommuting with `G`. This lemma is the anticommutation half (the phase `±i` does not affect
--   `sympForm`, see `sympForm_phaseMul_right`); the Hermiticity half is
--   `isSelfAdjoint_phaseMul_one_mul`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L312-L314
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L312-L314

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

theorem Lean4LPD.PauliString.sympForm_mul_self_right (G s : PauliString n) :
    sympForm G (G * s) = sympForm G s := by sorry
