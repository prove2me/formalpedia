-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdeal_iSup_le
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdeal_iSup_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:16:18.145806+00:00
-- url     : https://prove2.me/theorems/c58b88bd-439a-476f-9ddb-512e7ab54a7f
-- title:
--   Etale Coordinates: partial Deriv Ideal i Sup le
-- statement:
--   The Etale Coordinates construction uses the partial Deriv Ideal i Sup le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/ControlledTransformLogDerivativesInCharts.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/ControlledTransformLogDerivativesInCharts.lean#L16-L29

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_ControlledTransformLogDerivativesInCharts
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
variable (k : Type*) [CommRing k] (ι : Type*)
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdeal_iSup_le {κ : Sort*} (h : ι) (F : κ → Ideal S) :
    partialDerivIdeal k ι S h (⨆ j, F j) ≤ ⨆ j, partialDerivIdeal k ι S h (F j) := by sorry
