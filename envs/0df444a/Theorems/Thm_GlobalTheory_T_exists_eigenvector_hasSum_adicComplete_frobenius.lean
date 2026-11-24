-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_eigenvector_hasSum_adicComplete_frobenius
-- name    : GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:33:52.852087+00:00
-- url     : https://prove2.me/theorems/9fd85787-7cb3-47fa-8ad7-3024437220e6
-- title:
--   T: exists eigenvector has Sum adic Complete frobenius
-- statement:
--   The T construction uses the exists eigenvector has Sum adic Complete frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEigenvectorHasSumAdicCompleteFrobeniusStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEigenvectorHasSumAdicCompleteFrobeniusStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEigenvectorHasSumAdicCompleteFrobenius
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEigenvectorHasSumAdicCompleteFrobeniusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by sorry
