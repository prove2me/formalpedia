-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_DerivIdealBaseChange_map_derivIdeal
-- name    : FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange.map_derivIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:35.291563+00:00
-- url     : https://prove2.me/theorems/57df1fe6-7de4-4738-937d-514dfae7e5a0
-- title:
--   Deriv Ideal Base Change: map deriv Ideal
-- statement:
--   The Deriv Ideal Base Change construction uses the map deriv Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealFieldExtension.lean#L181-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealFieldExtension.lean#L181-L186

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealFieldExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (L : Type*) [CommRing L] [Algebra k L]
  (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S' : Type*) [CommRing S'] [Algebra L S'] [Algebra (MvPolynomial ι L) S']
  [IsScalarTower L (MvPolynomial ι L) S'] [Algebra.FormallyEtale (MvPolynomial ι L) S']
  [Algebra k S'] [IsScalarTower k L S']

theorem FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange.map_derivIdeal [Fintype ι] (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (J : Ideal S) :
    Ideal.map φ (derivIdeal k J) = derivIdeal L (Ideal.map φ J) := by sorry
