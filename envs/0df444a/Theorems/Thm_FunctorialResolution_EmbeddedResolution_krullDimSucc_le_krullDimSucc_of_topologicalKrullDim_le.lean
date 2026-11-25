-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le
-- name    : FunctorialResolution.EmbeddedResolution.krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:10.848084+00:00
-- url     : https://prove2.me/theorems/19347c78-bf72-4705-b0b6-0b65dcbb67a5
-- title:
--   Embedded Resolution: krull Dim Succ le krull Dim Succ of topological Krull Dim le
-- statement:
--   The Embedded Resolution construction uses the krull Dim Succ le krull Dim Succ of topological Krull Dim le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L29-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L29-L57

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le (X Y : Scheme.{u})
    (h : topologicalKrullDim ↥X ≤ topologicalKrullDim ↥Y)
    (hY : topologicalKrullDim ↥Y < ⊤) :
    krullDimSucc X ≤ krullDimSucc Y := by sorry
