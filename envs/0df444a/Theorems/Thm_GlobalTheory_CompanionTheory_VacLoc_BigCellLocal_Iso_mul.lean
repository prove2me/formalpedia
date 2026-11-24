-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_Iso_mul
-- name    : GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.Iso.mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:34.93967+00:00
-- url     : https://prove2.me/theorems/5d4b624b-c614-445b-98f3-1f36558d10f6
-- title:
--   Iso: mul
-- statement:
--   The Iso construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L18-L21

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
omit [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.Iso.mul {D₁ D₂ D₃ M N : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (h' : Iso σ D₂ D₃ N) : Iso σ D₁ D₃ (M * N) := by sorry
