-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_smul_partialDeriv_mem_tangentDerivations
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_smul_partialDeriv_mem_tangentDerivations
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:12.75764+00:00
-- url     : https://prove2.me/theorems/eb6c5c5f-d479-4b4c-b316-8b5d7d75616a
-- title:
--   Etale Coordinates: coord smul partial Deriv mem tangent Derivations
-- statement:
--   The Etale Coordinates construction uses the coord smul partial Deriv mem tangent Derivations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L14-L18

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
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
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_smul_partialDeriv_mem_tangentDerivations (h : ι) :
    coord k ι S h • partialDeriv k ι S h ∈
      tangentDerivations k (Ideal.span ({coord k ι S h} : Set S)) := by sorry
