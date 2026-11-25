-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_hasStrictNormalCrossingsWith_ker_cons_of_hasLocalCoordsOnSmoothHypersurface
-- name    : FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_ker_cons_of_hasLocalCoordsOnSmoothHypersurface
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:47.305977+00:00
-- url     : https://prove2.me/theorems/f731a17a-e319-4f82-83b8-cf897ad5eb6b
-- title:
--   Embedded Resolution: has Strict Normal Crossings With ker cons of has Local Coords On Smooth Hypersurface
-- statement:
--   The Embedded Resolution construction uses the has Strict Normal Crossings With ker cons of has Local Coords On Smooth Hypersurface property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L473-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L473-L596

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}} {k : Type u} [Field k]

theorem FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_ker_cons_of_hasLocalCoordsOnSmoothHypersurface [CharZero k] (p : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (H : P.IdealSheafData) (N : List P.IdealSheafData)
    (Z : H.subscheme.IdealSheafData)
    (hN : InStrictNormalCrossingPosition p (H :: N))
    (_hZ : HasStrictNormalCrossingsWith (H.subschemeι ≫ p) Z (N.map fun D => D.comap H.subschemeι))
    (hdata : HasLocalCoordsOnSmoothHypersurface p H N Z) :
    HasStrictNormalCrossingsWith p (Z.subschemeι ≫ H.subschemeι).ker (H :: N) := by sorry
