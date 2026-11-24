-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_mapCoeffAlgebra_isScalarTower
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.mapCoeffAlgebra_isScalarTower
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:45:59.516029+00:00
-- url     : https://prove2.me/theorems/58c11a8f-d991-4643-8d5d-33ed03ef13dd
-- title:
--   Etale Coordinates: map Coeff Algebra is Scalar Tower
-- statement:
--   The Etale Coordinates construction uses the map Coeff Algebra is Scalar Tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L200-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L200-L211

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
open MvPolynomial
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]
attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.mapCoeffAlgebra_isScalarTower [IsScalarTower k (MvPolynomial ι k) S] :
    IsScalarTower (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))
      (MvPolynomial κ S) := by sorry
