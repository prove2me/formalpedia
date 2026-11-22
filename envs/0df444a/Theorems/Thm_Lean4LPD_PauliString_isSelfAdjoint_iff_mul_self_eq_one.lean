-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_mul_self_eq_one
-- name    : Lean4LPD.PauliString.isSelfAdjoint_iff_mul_self_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:24.711344+00:00
-- url     : https://prove2.me/theorems/73d079ec-ce6c-4a10-91c8-928c03b1396d
-- title:
--   Pauli String: is Self Adjoint iff mul self eq one
-- statement:
--   **Hermiticity and involutivity coincide** for a Pauli string.
--
--   `Rotation.lean` needs both `G * G = 1` and `star G = G`, and in a general `*`-algebra the two are
--   **independent**: a self-adjoint element need not square to one (take `2` in `ℂ`), and an element
--   squaring to one need not be self-adjoint (take `!![1,1;0,-1]`). `Rotation.lean` notes the first of
--   those. For a Pauli string they coincide, because `star s = s⁻¹` (`star_eq_inv`): the string is
--   unitary, so self-adjointness *is* involutivity, and one hypothesis discharges both.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L400-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L400-L402

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

theorem Lean4LPD.PauliString.isSelfAdjoint_iff_mul_self_eq_one {s : PauliString n} :
    IsSelfAdjoint s ↔ s * s = 1 := by sorry
