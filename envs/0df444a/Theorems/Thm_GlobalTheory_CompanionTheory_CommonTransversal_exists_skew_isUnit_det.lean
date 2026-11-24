-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommonTransversal_exists_skew_isUnit_det
-- name    : GlobalTheory.CompanionTheory.CommonTransversal.exists_skew_isUnit_det
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:18.105505+00:00
-- url     : https://prove2.me/theorems/2c70d2b3-382b-4b80-b85b-a4a8ff4a40f3
-- title:
--   Common Transversal: exists skew is Unit det
-- statement:
--   The Common Transversal construction uses the exists skew is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsSkewOfDiagonal.lean#L7-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsSkewOfDiagonal.lean#L7-L91

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommonTransversal

theorem GlobalTheory.CompanionTheory.CommonTransversal.exists_skew_isUnit_det {F : Type} [Field F] (σ : F →+* F) {β : Type} [Fintype β]
    [DecidableEq β] (a b : Matrix β β F) (hσ : ∀ z, σ (σ z) = z) (hz : ∃ z, σ z ≠ z)
    (h : a * (b.map σ)ᵀ + b * (a.map σ)ᵀ = 0)
    (hv : ∀ v : β → F, Matrix.vecMul v a = 0 → Matrix.vecMul v b = 0 → v = 0) :
    ∃ s : Matrix β β F, (s.map σ)ᵀ = -s ∧ IsUnit (a + b * s).det := by sorry
