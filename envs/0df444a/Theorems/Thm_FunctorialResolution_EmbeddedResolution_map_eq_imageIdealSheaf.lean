-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_eq_imageIdealSheaf
-- name    : FunctorialResolution.EmbeddedResolution.map_eq_imageIdealSheaf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:44.697672+00:00
-- url     : https://prove2.me/theorems/654925f2-aed4-4194-ab34-4ed2c3f4a99f
-- title:
--   Embedded Resolution: map eq image Ideal Sheaf
-- statement:
--   The Embedded Resolution construction uses the map eq image Ideal Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/BlowupSequenceRelations.lean#L16-L17

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

theorem FunctorialResolution.EmbeddedResolution.map_eq_imageIdealSheaf {S X : Scheme.{u}} (f : S ⟶ X) (I : S.IdealSheafData) :
    I.map f = imageIdealSheaf f I := by sorry
