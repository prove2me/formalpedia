-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_strictTransform_of_comm_sq
-- name    : FunctorialResolution.EmbeddedResolution.imageIdealSheaf_strictTransform_of_comm_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:47:47.262217+00:00
-- url     : https://prove2.me/theorems/12969e18-d06e-4d67-9c3d-8f09475fc057
-- title:
--   Embedded Resolution: image Ideal Sheaf strict Transform of comm sq
-- statement:
--   The Embedded Resolution construction uses the image Ideal Sheaf strict Transform of comm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L115-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L115-L144

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

theorem FunctorialResolution.EmbeddedResolution.imageIdealSheaf_strictTransform_of_comm_sq {X X₁ Y Y₁ : Scheme.{u}}
    (φ : X₁ ⟶ X) (ψ : Y₁ ⟶ Y) (u : X ⟶ Y) (u₁ : X₁ ⟶ Y₁) [IsIso u] [IsIso u₁]
    (hsq : u₁ ≫ ψ = φ ≫ u) (Z D : X.IdealSheafData) :
    imageIdealSheaf u₁ (Blowup.strictTransform φ Z D)
      = Blowup.strictTransform ψ (imageIdealSheaf u Z) (imageIdealSheaf u D) := by sorry
