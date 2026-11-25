-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_openSubschemeKer_comap
-- name    : FunctorialResolution.EmbeddedResolution.openSubschemeKer_comap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:26.534157+00:00
-- url     : https://prove2.me/theorems/bb2511a0-fd55-4ff9-8c1e-eb397a2354e0
-- title:
--   Embedded Resolution: open Subscheme Ker comap
-- statement:
--   The Embedded Resolution construction uses the open Subscheme Ker comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L261-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L261-L304

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SubschemeMapFlatness
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

theorem FunctorialResolution.EmbeddedResolution.openSubschemeKer_comap {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (Z : X.IdealSheafData) (A : Set X) (hA : IsClosed A)
    (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (hWc : IsClosed (W : Set Z.subscheme))
    (hW'c : IsClosed (W' : Set (Z.comap g).subscheme))
    (hirr : ∀ w : Z.subscheme, IsIrreducible (connectedComponent w)) :
    openSubschemeKer (Z.comap g) W' = (openSubschemeKer Z W).comap g := by sorry
