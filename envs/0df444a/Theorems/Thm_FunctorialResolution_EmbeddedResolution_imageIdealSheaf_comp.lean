-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comp
-- name    : FunctorialResolution.EmbeddedResolution.imageIdealSheaf_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:16.940187+00:00
-- url     : https://prove2.me/theorems/03170d85-8d62-4889-82cf-6ff789ee7543
-- title:
--   Embedded Resolution: image Ideal Sheaf comp
-- statement:
--   The Embedded Resolution construction uses the image Ideal Sheaf comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean#L19-L21

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

theorem FunctorialResolution.EmbeddedResolution.imageIdealSheaf_comp {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) (I : W.IdealSheafData) :
    imageIdealSheaf (g ≫ w) I = imageIdealSheaf w (imageIdealSheaf g I) := by sorry
