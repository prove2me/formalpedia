-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_not_unitAt_two
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.not_unitAt_two
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:17:55.118298+00:00
-- url     : https://prove2.me/theorems/ef9ae8a0-335e-4113-8fd0-cce40e2ea75b
-- title:
--   Cpt Model: not unit At two
-- statement:
--   The Cpt Model construction uses the not unit At two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L180-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L180-L180

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory

theorem GlobalTheory.CompanionTheory.Ar.CptModel.not_unitAt_two : ¬ unitAt _ two (2 : ℚ) := by sorry
