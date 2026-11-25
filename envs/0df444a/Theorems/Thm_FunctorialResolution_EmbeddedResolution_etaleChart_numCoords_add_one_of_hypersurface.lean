-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChart_numCoords_add_one_of_hypersurface
-- name    : FunctorialResolution.EmbeddedResolution.etaleChart_numCoords_add_one_of_hypersurface
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:55.358945+00:00
-- url     : https://prove2.me/theorems/f5945cef-d9b8-41ce-9948-52bb98b26d50
-- title:
--   Embedded Resolution: etale Chart num Coords add one of hypersurface
-- statement:
--   The Embedded Resolution construction uses the etale Chart num Coords add one of hypersurface property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L172-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothHypersurfaceLocalCoordinates.lean#L172-L191

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

theorem FunctorialResolution.EmbeddedResolution.etaleChart_numCoords_add_one_of_hypersurface (p : P ⟶ Spec (CommRingCat.of k))
    (H : P.IdealSheafData)
    [AlgebraicGeometry.LocallyOfFiniteType (H.subschemeι ≫ p)]
    {U : P.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j₁ : Fin n)
    (hH : restrictIdeal H U = c.coordIdeal {j₁})
    {V : H.subscheme.Opens} (_hV : IsAffineOpen V) {m' : ℕ}
    (c' : EtaleChart (H.subschemeι ≫ p) V m')
    (y : H.subscheme) (hyU : y ∈ H.subschemeι ⁻¹ᵁ U) (hyV : y ∈ V) :
    m' + 1 = n := by sorry
