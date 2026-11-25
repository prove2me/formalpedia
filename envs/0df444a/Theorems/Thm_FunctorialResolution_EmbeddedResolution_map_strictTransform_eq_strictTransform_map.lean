-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_strictTransform_eq_strictTransform_map
-- name    : FunctorialResolution.EmbeddedResolution.map_strictTransform_eq_strictTransform_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:27.948713+00:00
-- url     : https://prove2.me/theorems/4059de54-89a3-4766-9735-2eebb01e9544
-- title:
--   Embedded Resolution: map strict Transform eq strict Transform map
-- statement:
--   The Embedded Resolution construction uses the map strict Transform eq strict Transform map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L160-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L160-L172

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
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

theorem FunctorialResolution.EmbeddedResolution.map_strictTransform_eq_strictTransform_map {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j] (Z D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    [IsClosedImmersion j₁] [IsNoetherian A₁] [IsNoetherian A'₁]
    (hsq : j₁ ≫ π' = π ≫ j)
    (hker : Scheme.Hom.ker j₁ = Blowup.strictTransform π' (Z.map j) (Scheme.Hom.ker j)) :
    (Blowup.strictTransform π Z D).map j₁ = Blowup.strictTransform π' (Z.map j) (D.map j) := by sorry
