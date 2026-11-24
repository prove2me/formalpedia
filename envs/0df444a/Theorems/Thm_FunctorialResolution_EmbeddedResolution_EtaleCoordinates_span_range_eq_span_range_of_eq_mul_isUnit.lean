-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_span_range_eq_span_range_of_eq_mul_isUnit
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.span_range_eq_span_range_of_eq_mul_isUnit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:02.391845+00:00
-- url     : https://prove2.me/theorems/3144d1d1-8ebe-4154-becc-4757f0e1505f
-- title:
--   Etale Coordinates: span range eq span range of eq mul is Unit
-- statement:
--   The Etale Coordinates construction uses the span range eq span range of eq mul is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/FormallyEtaleCoordinates.lean#L252-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/FormallyEtaleCoordinates.lean#L252-L266

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.span_range_eq_span_range_of_eq_mul_isUnit {A : Type*} [CommRing A] {n : ℕ}
    (y z c : Fin n → A) (hc : ∀ i, IsUnit (c i)) (hz : ∀ i, z i = y i * c i) :
    Ideal.span (Set.range z) = Ideal.span (Set.range y) := by sorry
