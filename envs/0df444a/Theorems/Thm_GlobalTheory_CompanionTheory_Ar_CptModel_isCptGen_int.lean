-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_isCptGen_int
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.isCptGen_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:17:49.917091+00:00
-- url     : https://prove2.me/theorems/707a4988-2456-4dee-8fa0-9ed63de95b8f
-- title:
--   Cpt Model: is Cpt Gen int
-- statement:
--   The Cpt Model construction uses the is Cpt Gen int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L160-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L160-L160

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.isCptGen_int : IsCptGen (pt (algebraMap ℤ ℚ)) := by sorry
