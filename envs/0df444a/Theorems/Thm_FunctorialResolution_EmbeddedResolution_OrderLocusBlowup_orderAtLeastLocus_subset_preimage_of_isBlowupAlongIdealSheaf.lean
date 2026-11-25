-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OrderLocusBlowup_orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf
-- name    : FunctorialResolution.EmbeddedResolution.OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:11.882922+00:00
-- url     : https://prove2.me/theorems/95fd77b9-c6f7-4baf-bfd5-3404051ddaed
-- title:
--   Order Locus Blowup: order At Least Locus subset preimage of is Blowup Along Ideal Sheaf
-- statement:
--   The Order Locus Blowup construction uses the order At Least Locus subset preimage of is Blowup Along Ideal Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/OrderUnderStalkIsomorphism.lean#L96-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/OrderUnderStalkIsomorphism.lean#L96-L114

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
open FunctorialResolution.EmbeddedResolution.OrderLocusBlowup

theorem FunctorialResolution.EmbeddedResolution.OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : X.IdealSheafData) (A₁ : X₁.IdealSheafData)
    (μ : ℕ) (hA : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π)
    (hZ : (Z.support : Set ↥X) ⊆ orderAtLeastLocus A μ) :
    orderAtLeastLocus A₁ μ ⊆ (⇑π.base) ⁻¹' orderAtLeastLocus A μ := by sorry
