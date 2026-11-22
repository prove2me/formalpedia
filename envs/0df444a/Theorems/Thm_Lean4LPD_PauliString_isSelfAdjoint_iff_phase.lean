-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase
-- name    : Lean4LPD.PauliString.isSelfAdjoint_iff_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:01.164948+00:00
-- url     : https://prove2.me/theorems/246a5e3d-8e83-4910-b604-63e39dab17d1
-- title:
--   Pauli String: is Self Adjoint iff phase
-- statement:
--   Hermiticity in coordinates: `i^{phase} X^x Z^z` is self-adjoint exactly when
--   `2·phase = 2⟪z,x⟫` in `ZMod 4` — equivalently, `phase ≡ ⟪z,x⟫ (mod 2)`, the standard criterion.
--
--   This fixes the parity of the phase and nothing more. Both solutions are admissible and they differ
--   by `2`, so a string and its negative are both self-adjoint; the criterion does not pick out a
--   canonical sign.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L410-L424
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L410-L424

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

theorem Lean4LPD.PauliString.isSelfAdjoint_iff_phase {s : PauliString n} :
    IsSelfAdjoint s ↔ signPhase (s.z ⬝ᵥ s.x) = 2 * s.phase := by sorry
