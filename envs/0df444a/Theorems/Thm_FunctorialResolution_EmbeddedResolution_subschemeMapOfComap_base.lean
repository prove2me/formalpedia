-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_subschemeMapOfComap_base
-- name    : FunctorialResolution.EmbeddedResolution.subschemeMapOfComap_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:52.440803+00:00
-- url     : https://prove2.me/theorems/16b892ee-f6a2-414e-8c57-1ddd83bcd46e
-- title:
--   Embedded Resolution: subscheme Map Of Comap base
-- statement:
--   The Embedded Resolution construction uses the subscheme Map Of Comap base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L58-L65

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

theorem FunctorialResolution.EmbeddedResolution.subschemeMapOfComap_base {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData)
    (y : (Z.comap g).subscheme) :
    Z.subschemeι.base ((subschemeMapOfComap g Z).base y) =
      g.base ((Z.comap g).subschemeι.base y) := by sorry
