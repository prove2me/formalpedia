-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_temperate_exp
-- name    : GlobalTheory.CompanionTheory.OM.SchDiff.temperate_exp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:57.789063+00:00
-- url     : https://prove2.me/theorems/4157f4a6-9f46-4d10-91a0-81759a60c569
-- title:
--   Sch Diff: temperate exp
-- statement:
--   The Sch Diff construction uses the temperate exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L211-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L211-L226

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OM GlobalTheory.CompanionTheory.OM.SchDiff

theorem GlobalTheory.CompanionTheory.OM.SchDiff.temperate_exp : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by sorry
