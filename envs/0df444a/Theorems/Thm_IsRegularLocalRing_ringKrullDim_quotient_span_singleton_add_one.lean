-- Prove2me | Theorems.Thm_IsRegularLocalRing_ringKrullDim_quotient_span_singleton_add_one
-- name    : IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:29.352798+00:00
-- url     : https://prove2.me/theorems/9a10b445-1dca-4a4e-a90d-5dd3f298e6bf
-- title:
--   Is Regular Local Ring: ring Krull Dim quotient span singleton add one
-- statement:
--   The Is Regular Local Ring construction uses the ring Krull Dim quotient span singleton add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/RegularLocalRing.lean#L282-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/RegularLocalRing.lean#L282-L287

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsRegularLocalRing
open IsLocalRing
universe u

theorem IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by sorry
