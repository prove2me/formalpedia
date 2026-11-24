-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_openSubschemeKer_eq_top
-- name    : FunctorialResolution.EmbeddedResolution.restrictIdeal_openSubschemeKer_eq_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:48.628692+00:00
-- url     : https://prove2.me/theorems/5e0bb88e-b221-49b8-9e54-1bec20fb8221
-- title:
--   Embedded Resolution: restrict Ideal open Subscheme Ker eq top
-- statement:
--   The Embedded Resolution construction uses the restrict Ideal open Subscheme Ker eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L233-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/IdealSheafOpenRestriction.lean#L233-L279

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

theorem FunctorialResolution.EmbeddedResolution.restrictIdeal_openSubschemeKer_eq_top {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (U : X.Opens)
    (hU : ∀ w : Z.subscheme, w ∈ W → Z.subschemeι.base w ∉ U) :
    restrictIdeal (openSubschemeKer Z W) U = ⊤ := by sorry
