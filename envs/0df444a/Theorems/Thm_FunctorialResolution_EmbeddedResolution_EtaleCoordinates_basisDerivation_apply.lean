-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:07.100436+00:00
-- url     : https://prove2.me/theorems/5d6a5707-0961-41d4-941e-f7415bda321e
-- title:
--   Etale Coordinates: basis Derivation apply
-- statement:
--   The Etale Coordinates construction uses the basis Derivation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleCoordinates.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleCoordinates.lean#L186-L188

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
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
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra (MvPolynomial ι k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
include ι

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply [Fintype ι] [DecidableEq ι] (i : ι) :
    basisDerivation k ι S i = partialDeriv k ι S i := by sorry
