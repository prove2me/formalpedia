-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_openSubschemeKer_eq_ker
-- name    : FunctorialResolution.EmbeddedResolution.openSubschemeKer_eq_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:46.379804+00:00
-- url     : https://prove2.me/theorems/5366461d-878b-4273-944d-ccaa2c289f39
-- title:
--   Embedded Resolution: open Subscheme Ker eq ker
-- statement:
--   The Embedded Resolution construction uses the open Subscheme Ker eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L21-L22

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
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

theorem FunctorialResolution.EmbeddedResolution.openSubschemeKer_eq_ker {X : Scheme.{u}} (Z : X.IdealSheafData) (W : Z.subscheme.Opens) :
    openSubschemeKer Z W = (Scheme.Opens.ι W ≫ Z.subschemeι).ker := by sorry
