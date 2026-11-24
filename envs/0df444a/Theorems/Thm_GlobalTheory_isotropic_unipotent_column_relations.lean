-- Prove2me | Theorems.Thm_GlobalTheory_isotropic_unipotent_column_relations
-- name    : GlobalTheory.isotropic_unipotent_column_relations
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:46.804725+00:00
-- url     : https://prove2.me/theorems/3b0f1adc-8942-4c81-a6d3-01f400695b08
-- title:
--   Global Theory: isotropic unipotent column relations
-- statement:
--   The Global Theory construction uses the isotropic unipotent column relations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianFlagUnipotentMatrixExistsSparse.lean#L6-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianFlagUnipotentMatrixExistsSparse.lean#L6-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagUnipotentMatrixExistsSparse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.isotropic_unipotent_column_relations : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by sorry
