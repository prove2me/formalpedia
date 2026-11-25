-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_imageIdealSheaf
-- name    : FunctorialResolution.EmbeddedResolution.comap_imageIdealSheaf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:01.706243+00:00
-- url     : https://prove2.me/theorems/6b661696-2380-493e-89a2-fd06f01e39f2
-- title:
--   Embedded Resolution: comap image Ideal Sheaf
-- statement:
--   The Embedded Resolution construction uses the comap image Ideal Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L37-L41

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

theorem FunctorialResolution.EmbeddedResolution.comap_imageIdealSheaf {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    (imageIdealSheaf f J).comap f = J := by sorry
