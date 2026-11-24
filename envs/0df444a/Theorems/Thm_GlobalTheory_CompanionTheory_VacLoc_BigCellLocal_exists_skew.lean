-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_exists_skew
-- name    : GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.exists_skew
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:25.777201+00:00
-- url     : https://prove2.me/theorems/a5a33942-f101-42f1-8df7-0f85d3de2e52
-- title:
--   Big Cell Local: exists skew
-- statement:
--   The Big Cell Local construction uses the exists skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L65-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L65-L110

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]

theorem GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.exists_skew [IsLocalRing A] (hσ : ∀ z, σ (σ z) = z) {w : A} (hw : w + σ w = 1) {z : A} (hz : IsUnit (z - σ z))
    {a b c d : Matrix β β A} (h : Iso σ (Wm A β) (Wm A β) (fromBlocks a b c d)) :
    ∃ s : Matrix β β A, s.map σ = -sᵀ ∧ IsUnit (a + s * c).det := by sorry
