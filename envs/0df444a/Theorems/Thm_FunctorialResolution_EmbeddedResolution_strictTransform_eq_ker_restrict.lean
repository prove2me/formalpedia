-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_restrict
-- name    : FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_restrict
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:48:49.695341+00:00
-- url     : https://prove2.me/theorems/3d25176c-5ce9-4002-937c-e2c17311d2ea
-- title:
--   Embedded Resolution: strict Transform eq ker restrict
-- statement:
--   The Embedded Resolution construction uses the strict Transform eq ker restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L253-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransform.lean#L253-L268

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
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

theorem FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_restrict {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ : X.IdealSheafData) :
    Blowup.strictTransform f W D₁ =
      (((D₁.comap (Scheme.Opens.ι W.support.compl)).comap
            (f ∣_ W.support.compl)).subschemeι ≫
          Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl)).ker := by sorry
