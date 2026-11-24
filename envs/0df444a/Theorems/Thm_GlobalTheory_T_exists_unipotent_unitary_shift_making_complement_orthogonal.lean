-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unipotent_unitary_shift_making_complement_orthogonal
-- name    : GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:58.093267+00:00
-- url     : https://prove2.me/theorems/d0074fdf-7b3b-4dbd-8de4-418df6767c9a
-- title:
--   T: exists unipotent unitary shift making complement orthogonal
-- statement:
--   The T construction uses the exists unipotent unitary shift making complement orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLeviElementIsotropicOrthogonalComplexStatement.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLeviElementIsotropicOrthogonalComplexStatement.lean#L6-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLeviElementIsotropicOrthogonalComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLeviElementIsotropicOrthogonalComplexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unipotent_unitary_shift_making_complement_orthogonal : ∀ (n a b : ℕ) (J Q : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → Q.PosDef →
    ∀ (X₁ Y₁ : Matrix (Fin n) (Fin a) ℂ) (Xb Yb : Matrix (Fin n) (Fin b) ℂ),
      X₁.conjTranspose * J * X₁ = 0 → X₁.conjTranspose * J * Xb = 0 → Xb.conjTranspose * J * Xb = 0 →
      X₁.conjTranspose * J * Y₁ = 1 → X₁.conjTranspose * J * Yb = 0 → Yb.conjTranspose * J * Yb = 0 →
      Xb.conjTranspose * J * Yb = 1 →
    ∃ (u₂ : GL (Fin n) ℂ) (A : Matrix (Fin a) (Fin b) ℂ), (u₂.1).conjTranspose * J * u₂.1 = J ∧
      u₂.1 * X₁ = X₁ ∧ u₂.1 * Xb = Xb + X₁ * A ∧ u₂.1 * Yb = Yb ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₁.conjTranspose * J) v = 0 →
        Matrix.mulVec u₂.1 v = v + Matrix.mulVec X₁ (Matrix.mulVec A (Matrix.mulVec (Yb.conjTranspose * J) v))) ∧
      X₁.conjTranspose * Q * (Xb + X₁ * A) = 0 := by sorry
