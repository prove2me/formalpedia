-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SchrLaw_goodChar_isLocallyConstant
-- name    : GlobalTheory.CompanionTheory.SchrLaw.goodChar_isLocallyConstant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:11:55.826317+00:00
-- url     : https://prove2.me/theorems/ce04aa36-da47-4e07-b6bc-c2a369ab7d31
-- title:
--   Schr Law: good Char is Locally Constant
-- statement:
--   The Schr Law construction uses the good Char is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/GoodCharIsLocallyConstant.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/GoodCharIsLocallyConstant.lean#L8-L24

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchrLaw

theorem GlobalTheory.CompanionTheory.SchrLaw.goodChar_isLocallyConstant {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) : IsLocallyConstant (ψ : R → ℂ) := by sorry
