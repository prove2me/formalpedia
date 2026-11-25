-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_isDomain_stalk
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.isDomain_stalk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:45.175808+00:00
-- url     : https://prove2.me/theorems/607d5587-b295-4e74-a592-01851aaf22bc
-- title:
--   Cpt Model: is Domain stalk
-- statement:
--   The Cpt Model construction uses the is Domain stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L37-L39

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.isDomain_stalk {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) := by sorry
