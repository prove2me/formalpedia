-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_injective_of_isCptGen
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.injective_of_isCptGen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:17:59.29721+00:00
-- url     : https://prove2.me/theorems/71db65c0-cbc8-481b-ac80-697a241fd65f
-- title:
--   Cpt Model: injective of is Cpt Gen
-- statement:
--   The Cpt Model construction uses the injective of is Cpt Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L148-L154

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
variable {R K : Type} [CommRing R] [Field K]

theorem GlobalTheory.CompanionTheory.Ar.CptModel.injective_of_isCptGen [IsDomain R] (φ : R →+* K) (h : IsCptGen (pt φ)) :
    Function.Injective φ := by sorry
