-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:19.040713+00:00
-- url     : https://prove2.me/theorems/11707328-34a8-4b98-87f3-7115b5f1f54e
-- title:
--   Etale Coordinates: deriv Ideal Iterate le i Sup log Deriv Ideal Iterate partial Deriv Ideal Iterate
-- statement:
--   The Etale Coordinates construction uses the deriv Ideal Iterate le i Sup log Deriv Ideal Iterate partial Deriv Ideal Iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L220-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L220-L249

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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate [Fintype ι] [DecidableEq ι]
    (h : ι) (n : ℕ) (J : Ideal S) :
    derivIdealIterate k n J ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n - l)
          (partialDerivIdealIterate k ι S h l J) := by sorry
