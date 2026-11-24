-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_schemeAtIsoOfEq_hom_projectionToBase
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.schemeAtIsoOfEq_hom_projectionToBase
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:32.72327+00:00
-- url     : https://prove2.me/theorems/e30aaba5-9dfc-4634-8bc5-10b62cc032f4
-- title:
--   Sequence Of Blowups: scheme At Iso Of Eq hom projection To Base
-- statement:
--   The Sequence Of Blowups construction uses the scheme At Iso Of Eq hom projection To Base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean#L21-L24

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.schemeAtIsoOfEq_hom_projectionToBase (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) :
    (s.schemeAtIsoOfEq h).hom ≫ s.projectionToBase j = s.projectionToBase i := by sorry
