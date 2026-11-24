-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:07.677604+00:00
-- url     : https://prove2.me/theorems/65a4a291-b1fe-4f16-bf72-4158dc619ebe
-- title:
--   Etale Coordinates: algebra Map X inr
-- statement:
--   The Etale Coordinates construction uses the algebra Map X inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L174-L177

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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr (j : κ) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) (X (Sum.inr j))
      = (X j : MvPolynomial κ S) := by sorry
