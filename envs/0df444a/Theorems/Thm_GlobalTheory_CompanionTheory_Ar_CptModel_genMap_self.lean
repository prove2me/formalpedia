-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_self
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.genMap_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:37.480472+00:00
-- url     : https://prove2.me/theorems/9afea944-699a-4c7d-95a8-cae81d23cc95
-- title:
--   Cpt Model: gen Map self
-- statement:
--   The Cpt Model construction uses the gen Map self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L16-L21

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

theorem GlobalTheory.CompanionTheory.Ar.CptModel.genMap_self (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    genMap ξ (self ξ) = (Scheme.stalkClosedPointTo ξ).hom := by sorry
