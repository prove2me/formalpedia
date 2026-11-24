-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_eq_ker
-- name    : FunctorialResolution.EmbeddedResolution.imageIdealSheaf_eq_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:07.4768+00:00
-- url     : https://prove2.me/theorems/7193cec6-4764-46f4-8535-82df144f1176
-- title:
--   Embedded Resolution: image Ideal Sheaf eq ker
-- statement:
--   The Embedded Resolution construction uses the image Ideal Sheaf eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean#L23-L24

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
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

theorem FunctorialResolution.EmbeddedResolution.imageIdealSheaf_eq_ker {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) :
    imageIdealSheaf σ I = (I.subschemeι ≫ σ).ker := by sorry
