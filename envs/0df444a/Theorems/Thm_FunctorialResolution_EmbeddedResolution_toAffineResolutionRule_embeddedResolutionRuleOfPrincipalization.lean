-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization
-- name    : FunctorialResolution.EmbeddedResolution.toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:23.874302+00:00
-- url     : https://prove2.me/theorems/e52b72ed-8827-49f5-91c9-fc691b9d2199
-- title:
--   Embedded Resolution: to Affine Resolution Rule embedded Resolution Rule Of Principalization
-- statement:
--   The Embedded Resolution construction uses the to Affine Resolution Rule embedded Resolution Rule Of Principalization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/EmbeddedResolutionRuleOfPrincipalization.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/EmbeddedResolutionRuleOfPrincipalization.lean#L35-L42

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsNil
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRuleOfPrincipalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) :
    (embeddedResolutionRuleOfPrincipalization A h).toAffineResolutionRule (affineSpaceEmbeddingChoice hemb hsnc hsm) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw := by sorry
