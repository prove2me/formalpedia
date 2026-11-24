-- Prove2me | Theorems.Thm_GlobalTheory_QFam_QAllSubring_sum
-- name    : GlobalTheory.QFam.QAllSubring.sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:30:04.112936+00:00
-- url     : https://prove2.me/theorems/677d8ce1-8978-42b4-bc1a-ae8d02dc7c10
-- title:
--   QAll Subring: sum
-- statement:
--   The QAll Subring construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionCoeffsInSubringRingClosed.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionCoeffsInSubringRingClosed.lean#L91-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam GlobalTheory.QFam.QAllSubring
variable {R : Subring ℂ} {N : ℕ}
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
variable {R : Subring ℂ} {N : ℕ}

theorem GlobalTheory.QFam.QAllSubring.sum {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ := by sorry
