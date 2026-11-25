-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_TrivRed_mono
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.TrivRed.mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:21.645846+00:00
-- url     : https://prove2.me/theorems/ed6253c1-e84b-4acf-bc99-0d6a6c24afe4
-- title:
--   Triv Red: mono
-- statement:
--   The Triv Red construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L97-L104

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem GlobalTheory.CompanionTheory.Ar.Flat.TrivRed.mono {L : Lat ξ E} {ϖ ϖ' : Ω} (h : TrivRed L ϖ) (hs : zeroSet ξ ϖ' ⊆ zeroSet ξ ϖ) :
    TrivRed L ϖ' := by sorry
