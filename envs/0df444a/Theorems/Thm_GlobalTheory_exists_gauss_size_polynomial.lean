-- Prove2me | Theorems.Thm_GlobalTheory_exists_gauss_size_polynomial
-- name    : GlobalTheory.exists_gauss_size_polynomial
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:14.239829+00:00
-- url     : https://prove2.me/theorems/898dc2fb-898f-432a-9e39-9fce362a2b11
-- title:
--   Global Theory: exists gauss size polynomial
-- statement:
--   The Global Theory construction uses the exists gauss size polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsogenyNumeratorCoeffNormLeOne.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsogenyNumeratorCoeffNormLeOne.lean#L6-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsogenyNumeratorCoeffNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.exists_gauss_size_polynomial (K : Type) [NormedField K] [IsUltrametricDist K] :
    ∃ G : K[X] → ℝ, (∀ p, 0 ≤ G p) ∧ (∀ p i, ‖p.coeff i‖ ≤ G p) ∧
      (∀ p r, (∀ i, ‖p.coeff i‖ ≤ r) → G p ≤ r) ∧
      (∀ p q, G (p * q) = G p * G q) ∧ (∀ p q, G (p + q) ≤ max (G p) (G q)) ∧
      (∀ a, G (C a) = ‖a‖) ∧ G X = 1 := by sorry
