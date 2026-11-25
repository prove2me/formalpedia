-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_BlowupSequenceData_ofSequenceOfBlowups_projectionToBase
-- name    : FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups_projectionToBase
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:56.587608+00:00
-- url     : https://prove2.me/theorems/52d0875e-20b3-4c74-a0e2-8cbe45055874
-- title:
--   Blowup Sequence Data: of Sequence Of Blowups projection To Base
-- statement:
--   The Blowup Sequence Data construction uses the of Sequence Of Blowups projection To Base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean#L229-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean#L229-L241

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

theorem FunctorialResolution.EmbeddedResolution.BlowupSequenceData.ofSequenceOfBlowups_projectionToBase (s : SequenceOfBlowups X) (i : ℕ) : projectionToBase (ofSequenceOfBlowups s) i = s.projectionToBase i := by sorry
