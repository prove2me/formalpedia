-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq
-- name    : FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:17:37.565543+00:00
-- url     : https://prove2.me/theorems/9162cbcf-927e-41cf-9550-2c3306759fe8
-- title:
--   Embedded Resolution: empty Marked Blowup Sequence Data to Blowup Sequence Data eq
-- statement:
--   The Embedded Resolution construction uses the empty Marked Blowup Sequence Data to Blowup Sequence Data eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean#L489-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean#L489-L492

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_BlowupSequenceData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData = emptyBlowupSequenceData X := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq
