-- Prove2me | Theorems.Thm_GlobalTheory_radical_elt_moving_dual_to_majorant
-- name    : GlobalTheory.radical_elt_moving_dual_to_majorant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:52.943112+00:00
-- url     : https://prove2.me/theorems/73ce8c33-837a-4cd5-be96-71879c5444b1
-- title:
--   Global Theory: radical elt moving dual to majorant
-- statement:
--   The Global Theory construction uses the radical elt moving dual to majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RadicalEltMovingDualToMajorant.lean#L7-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RadicalEltMovingDualToMajorant.lean#L7-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open Matrix
open GlobalTheory

theorem GlobalTheory.radical_elt_moving_dual_to_majorant (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.conjTranspose = J) (hθ : θ * θ = 1) (hQ : (J * θ).PosDef)
    (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ) (hXX : X₂.conjTranspose * J * X₂ = 0)
    (hYY : Y₂.conjTranspose * J * Y₂ = 0) (hXY : X₂.conjTranspose * J * Y₂ = 1) :
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by sorry
