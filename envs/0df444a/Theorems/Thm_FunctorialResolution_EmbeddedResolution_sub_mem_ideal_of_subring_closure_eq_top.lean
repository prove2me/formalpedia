-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_sub_mem_ideal_of_subring_closure_eq_top
-- name    : FunctorialResolution.EmbeddedResolution.sub_mem_ideal_of_subring_closure_eq_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:05.335219+00:00
-- url     : https://prove2.me/theorems/16bab9eb-8897-49e7-9296-75f61cfe665f
-- title:
--   Embedded Resolution: sub mem ideal of subring closure eq top
-- statement:
--   The Embedded Resolution construction uses the sub mem ideal of subring closure eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L67-L73

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
variable {B A : Type u} [CommRing B] [CommRing A]

theorem FunctorialResolution.EmbeddedResolution.sub_mem_ideal_of_subring_closure_eq_top (f g : B →+* A) (J : Ideal A) (S : Set B)
    (hS : Subring.closure S = ⊤) (hmem : ∀ b ∈ S, f b - g b ∈ J) (b : B) :
    f b - g b ∈ J := by sorry
