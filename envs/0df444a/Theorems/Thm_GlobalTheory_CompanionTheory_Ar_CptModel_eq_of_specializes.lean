-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_eq_of_specializes
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.eq_of_specializes
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:17:47.888124+00:00
-- url     : https://prove2.me/theorems/e4ac7630-8d0c-4743-8ede-ded1227f7086
-- title:
--   Cpt Model: eq of specializes
-- statement:
--   The Cpt Model construction uses the eq of specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L45-L55

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
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem GlobalTheory.CompanionTheory.Ar.CptModel.eq_of_specializes {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) {y : X}
    (hy : y ⤳ genPt ξ) : y = genPt ξ := by sorry
