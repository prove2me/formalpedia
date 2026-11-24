-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_sumEvalAlgebra_isScalarTower
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.sumEvalAlgebra_isScalarTower
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:10.363813+00:00
-- url     : https://prove2.me/theorems/e79a9cf2-7b79-444b-9c16-d6b76ee52bf1
-- title:
--   Etale Coordinates: sum Eval Algebra is Scalar Tower
-- statement:
--   The Etale Coordinates construction uses the sum Eval Algebra is Scalar Tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L162-L164

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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.sumEvalAlgebra_isScalarTower :
    IsScalarTower k (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) := by sorry
