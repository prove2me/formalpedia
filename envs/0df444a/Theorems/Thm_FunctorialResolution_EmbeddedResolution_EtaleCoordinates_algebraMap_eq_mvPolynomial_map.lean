-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_eq_mvPolynomial_map
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_eq_mvPolynomial_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:14.940463+00:00
-- url     : https://prove2.me/theorems/b85a66bb-515f-4622-acfb-4bcd4970319c
-- title:
--   Etale Coordinates: algebra Map eq mv Polynomial map
-- statement:
--   The Etale Coordinates construction uses the algebra Map eq mv Polynomial map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L112-L114

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
  [Algebra (MvPolynomial ι k) S]
attribute [local instance] mapCoeffAlgebra

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_eq_mvPolynomial_map (p : MvPolynomial κ (MvPolynomial ι k)) :
    algebraMap (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) p
      = MvPolynomial.map (algebraMap (MvPolynomial ι k) S) p := by sorry
