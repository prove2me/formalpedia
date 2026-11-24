-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_BlowupSequenceData_toSequenceOfBlowups_schemeAt
-- name    : FunctorialResolution.EmbeddedResolution.BlowupSequenceData.toSequenceOfBlowups_schemeAt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:17:36.069327+00:00
-- url     : https://prove2.me/theorems/ec730a6f-e882-40db-b189-20bc83f0d226
-- title:
--   Blowup Sequence Data: to Sequence Of Blowups scheme At
-- statement:
--   The Blowup Sequence Data construction uses the to Sequence Of Blowups scheme At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean#L171-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean#L171-L171

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
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData
variable {X : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.BlowupSequenceData.toSequenceOfBlowups_schemeAt (d : BlowupSequenceData X) (i : ℕ) : d.toSequenceOfBlowups.schemeAt i = d.obj i := by sorry
