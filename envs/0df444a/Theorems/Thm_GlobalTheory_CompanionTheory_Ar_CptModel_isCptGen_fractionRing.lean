-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_isCptGen_fractionRing
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.isCptGen_fractionRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:35.727707+00:00
-- url     : https://prove2.me/theorems/1f85ffeb-37a5-4749-9f00-365c5e4c36aa
-- title:
--   Cpt Model: is Cpt Gen fraction Ring
-- statement:
--   The Cpt Model construction uses the is Cpt Gen fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L135-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L135-L146

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.isCptGen_fractionRing [IsDomain R] [Algebra R K] [IsFractionRing R K] :
    IsCptGen (pt (algebraMap R K)) := by sorry
