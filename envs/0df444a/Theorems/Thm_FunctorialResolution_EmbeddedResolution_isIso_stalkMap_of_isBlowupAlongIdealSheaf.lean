-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIso_stalkMap_of_isBlowupAlongIdealSheaf
-- name    : FunctorialResolution.EmbeddedResolution.isIso_stalkMap_of_isBlowupAlongIdealSheaf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:12:53.905972+00:00
-- url     : https://prove2.me/theorems/eaf73056-a98d-45eb-8df5-a71d0a6310e4
-- title:
--   Embedded Resolution: is Iso stalk Map of is Blowup Along Ideal Sheaf
-- statement:
--   The Embedded Resolution construction uses the is Iso stalk Map of is Blowup Along Ideal Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/OrderUnderStalkIsomorphism.lean#L57-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/OrderUnderStalkIsomorphism.lean#L57-L92

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_OrderUnderStalkIsomorphism
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
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.isIso_stalkMap_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (h : Blowup.IsBlowupAlongIdealSheaf π Z) (x : X₁) (hx : π.base x ∉ Z.support) :
    IsIso (π.stalkMap x) := by sorry
