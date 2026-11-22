-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_commute_or_anticommute
-- name    : Lean4LPD.PauliString.commute_or_anticommute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:24.903277+00:00
-- url     : https://prove2.me/theorems/f96eb7bc-24ad-41f2-b29d-7d60cb111c9b
-- title:
--   Pauli String: commute or anticommute
-- statement:
--   **Any two Pauli strings either commute or anticommute.** This is the fact that makes the
--   two cases `[G,P] = 0` and `{G,P} = 0` of `apd:eq:pauli_rotation_branch` exhaustive, so that a
--   Pauli rotation acting on a Pauli operator either leaves it unchanged or splits it into exactly
--   two terms. Here anticommutation is spelled `s * t = phaseMul 2 (t * s)`, that is
--   `s t = i² · t s = −t s`.
--
--   This is the hypothesis-level companion to `Lean4LPD.rot_conj_of_commute` and
--   `Lean4LPD.rot_conj_of_anticommute`: those two theorems cover a commuting and an anticommuting
--   generator, and without this lemma nothing rules out a pair of Paulis that is neither.
--   `Pauli/Matrix.lean` transports it to operators as `toMatrix_commute_or_anticommute`, which is the
--   form `Rotation.lean` consumes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L385-L389
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Basic.lean#L385-L389

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

theorem Lean4LPD.PauliString.commute_or_anticommute (s t : PauliString n) :
    Commute s t ∨ s * t = phaseMul 2 (t * s) := by sorry
