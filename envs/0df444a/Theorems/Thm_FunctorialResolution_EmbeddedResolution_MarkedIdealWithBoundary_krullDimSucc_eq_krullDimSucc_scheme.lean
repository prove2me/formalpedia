-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedIdealWithBoundary_krullDimSucc_eq_krullDimSucc_scheme
-- name    : FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.krullDimSucc_eq_krullDimSucc_scheme
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:45.88691+00:00
-- url     : https://prove2.me/theorems/f73c09d2-167d-495b-84f1-8edf96fadeb5
-- title:
--   Marked Ideal With Boundary: krull Dim Succ eq krull Dim Succ scheme
-- statement:
--   The Marked Ideal With Boundary construction uses the krull Dim Succ eq krull Dim Succ scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L81-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L81-L81

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
attribute [instance] MarkedIdealWithBoundary.instField

theorem FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.krullDimSucc_eq_krullDimSucc_scheme (T : MarkedIdealWithBoundary.{u}) : T.krullDimSucc = EmbeddedResolution.krullDimSucc T.scheme := by sorry
