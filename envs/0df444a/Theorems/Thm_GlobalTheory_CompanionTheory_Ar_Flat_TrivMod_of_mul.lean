-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_TrivMod_of_mul
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.TrivMod.of_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:01.476482+00:00
-- url     : https://prove2.me/theorems/cb731eab-c1f7-56ab-bc96-d03db7d9a1af
-- title:
--   Triv Mod: of mul
-- statement:
--   The Triv Mod construction uses the of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L87-L95

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.TrivMod.of_mul {L : Lat ξ E} {ϖ a : Ω} (hϖ : ∀ p, ϖ ∈ regAt ξ p) (ha : ∀ p, a ∈ regAt ξ p)
    (h : TrivMod L (ϖ * a)) : TrivMod L ϖ := by sorry
