-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_DerivIdealBaseChange_partialDeriv_mem_map_derivIdeal
-- name    : FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange.partialDeriv_mem_map_derivIdeal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:48.525612+00:00
-- url     : https://prove2.me/theorems/8333c064-e874-40a9-8f8e-f067ec064cbb
-- title:
--   Deriv Ideal Base Change: partial Deriv mem map deriv Ideal
-- statement:
--   The Deriv Ideal Base Change construction uses the partial Deriv mem map deriv Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealFieldExtension.lean#L145-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealFieldExtension.lean#L145-L164

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

theorem FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange.partialDeriv_mem_map_derivIdeal (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (i : ι) (J : Ideal S)
    {g : S'} (hg : g ∈ Ideal.map φ J) :
    partialDeriv L ι S' i g ∈ Ideal.map φ (derivIdeal k J) := by sorry
