-- Prove2me | Theorems.Thm_GlobalTheory_abssum_eigen_lim
-- name    : GlobalTheory.abssum_eigen_lim
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:27.112845+00:00
-- url     : https://prove2.me/theorems/ca4a24f8-b865-431a-9c2b-4cda49874af6
-- title:
--   Global Theory: abssum eigen lim
-- statement:
--   The Global Theory construction uses the abssum eigen lim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEigenvectorHasSumAdicCompleteFrobenius.lean#L6-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEigenvectorHasSumAdicCompleteFrobenius.lean#L6-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEigenvectorHasSumAdicCompleteFrobenius
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

theorem GlobalTheory.abssum_eigen_lim : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by sorry
