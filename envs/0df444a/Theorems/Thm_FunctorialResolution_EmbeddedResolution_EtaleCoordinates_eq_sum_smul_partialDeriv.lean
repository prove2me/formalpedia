-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_eq_sum_smul_partialDeriv
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.eq_sum_smul_partialDeriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:04.815309+00:00
-- url     : https://prove2.me/theorems/611a20af-b50c-45ac-9c0a-b9fbce087a65
-- title:
--   Etale Coordinates: eq sum smul partial Deriv
-- statement:
--   The Etale Coordinates construction uses the eq sum smul partial Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleCoordinates.lean#L139-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleCoordinates.lean#L139-L157

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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.eq_sum_smul_partialDeriv [Fintype ι] (D : Derivation k S S) :
    D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by sorry
