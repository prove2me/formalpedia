-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_Iso_inv
-- name    : GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.Iso.inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:23.463691+00:00
-- url     : https://prove2.me/theorems/25ca3878-7f43-44ca-ba62-8b7e9daca206
-- title:
--   Iso: inv
-- statement:
--   The Iso construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L23-L29

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
variable {A : Type} [CommRing A] (σ : A →+* A) {ι : Type} [Fintype ι] [DecidableEq ι]
variable {σ}

theorem GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.Iso.inv {D₁ D₂ M N : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (hN : M * N = 1) : Iso σ D₂ D₁ N := by sorry
