-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_not_isCptGen_real
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.not_isCptGen_real
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:49.571278+00:00
-- url     : https://prove2.me/theorems/c4fbe021-b653-4657-bbb9-cc32bbd2e5e8
-- title:
--   Cpt Model: not is Cpt Gen real
-- statement:
--   The Cpt Model construction uses the not is Cpt Gen real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L192-L196

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.not_isCptGen_real : ¬ IsCptGen (pt (algebraMap ℤ ℝ)) := by sorry
