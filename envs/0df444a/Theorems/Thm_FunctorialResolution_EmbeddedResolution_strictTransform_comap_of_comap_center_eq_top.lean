-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_strictTransform_comap_of_comap_center_eq_top
-- name    : FunctorialResolution.EmbeddedResolution.strictTransform_comap_of_comap_center_eq_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:22.492463+00:00
-- url     : https://prove2.me/theorems/86a98d4d-b451-5053-b28d-7f58e2fe7f4a
-- title:
--   Embedded Resolution: strict Transform comap of comap center eq top
-- statement:
--   The Embedded Resolution construction uses the strict Transform comap of comap center eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean#L40-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean#L40-L65

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.strictTransform_comap_of_comap_center_eq_top {X X₁ B : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (g : B ⟶ X₁)
    (hg : (Z.comap π).comap g = ⊤) :
    (Blowup.strictTransform π Z D).comap g = (D.comap π).comap g := by sorry
