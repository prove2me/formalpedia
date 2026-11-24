-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comp_comap_of_isIso
-- name    : FunctorialResolution.EmbeddedResolution.imageIdealSheaf_comp_comap_of_isIso
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:47:54.448007+00:00
-- url     : https://prove2.me/theorems/10492111-29d1-4881-bb64-ef98b56ee136
-- title:
--   Embedded Resolution: image Ideal Sheaf comp comap of is Iso
-- statement:
--   The Embedded Resolution construction uses the image Ideal Sheaf comp comap of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L72-L77

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
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

theorem FunctorialResolution.EmbeddedResolution.imageIdealSheaf_comp_comap_of_isIso {A B C : Scheme.{u}} (w : A ⟶ B) [IsIso w] (g : B ⟶ C)
    (I : B.IdealSheafData) :
    imageIdealSheaf (w ≫ g) (I.comap w) = imageIdealSheaf g I := by sorry
