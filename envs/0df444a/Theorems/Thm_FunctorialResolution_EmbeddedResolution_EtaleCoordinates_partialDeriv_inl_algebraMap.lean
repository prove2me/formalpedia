-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_inl_algebraMap
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_inl_algebraMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:06.335042+00:00
-- url     : https://prove2.me/theorems/3d5fb411-a7f4-44bc-bca2-cc2dcd8b3d55
-- title:
--   Etale Coordinates: partial Deriv inl algebra Map
-- statement:
--   The Etale Coordinates construction uses the partial Deriv inl algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealEtaleBaseChange.lean#L74-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealEtaleBaseChange.lean#L74-L99

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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_inl_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (i : ι) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inl i) (algebraMap S T s)
      = algebraMap S T (partialDeriv k ι S i s) := by sorry
