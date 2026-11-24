-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_unitAt_three
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.unitAt_three
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:18:10.483381+00:00
-- url     : https://prove2.me/theorems/84018c89-0a80-4acf-9bc8-0722d5bd6189
-- title:
--   Cpt Model: unit At three
-- statement:
--   The Cpt Model construction uses the unit At three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L182-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L182-L186

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.unitAt_three : unitAt _ two (3 : ℚ) := by sorry
