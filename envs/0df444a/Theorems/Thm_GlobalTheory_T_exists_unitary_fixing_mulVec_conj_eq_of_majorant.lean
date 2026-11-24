-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unitary_fixing_mulVec_conj_eq_of_majorant
-- name    : GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:55.175942+00:00
-- url     : https://prove2.me/theorems/bdc54e3b-5d9d-4f14-ad97-008773c4c93e
-- title:
--   T: exists unitary fixing mul Vec conj eq of majorant
-- statement:
--   The T construction uses the exists unitary fixing mul Vec conj eq of majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RadicalEltMovingDualToMajorantStatement.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RadicalEltMovingDualToMajorantStatement.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorantStatement
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

theorem GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant : ∀ (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → θ * θ = 1 → (J * θ).PosDef →
    ∀ (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ), X₂.conjTranspose * J * X₂ = 0 → Y₂.conjTranspose * J * Y₂ = 0 →
      X₂.conjTranspose * J * Y₂ = 1 →
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 → ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by sorry
