-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_unitAt_iff
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.unitAt_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:17:55.206362+00:00
-- url     : https://prove2.me/theorems/42195158-a151-423a-a9dc-bda8a902c41d
-- title:
--   Cpt Model: unit At iff
-- statement:
--   The Cpt Model construction uses the unit At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L23-L35

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.unitAt_iff (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ s : X.presheaf.stalk p.1, IsUnit s ∧ genMap ξ p s = a := by sorry
