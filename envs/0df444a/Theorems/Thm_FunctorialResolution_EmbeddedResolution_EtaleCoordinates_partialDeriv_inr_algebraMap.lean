-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_inr_algebraMap
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_inr_algebraMap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:23.314253+00:00
-- url     : https://prove2.me/theorems/0bccf56c-7150-44e0-8c25-d4c55047fb9f
-- title:
--   Etale Coordinates: partial Deriv inr algebra Map
-- statement:
--   The Etale Coordinates construction uses the partial Deriv inr algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealEtaleBaseChange.lean#L50-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealEtaleBaseChange.lean#L50-L72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_inr_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (j : κ) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inr j) (algebraMap S T s) = 0 := by sorry
