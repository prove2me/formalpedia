-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_biInf_span_singleton
-- name    : FunctorialResolution.EmbeddedResolution.isRadical_biInf_span_singleton
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:37.515958+00:00
-- url     : https://prove2.me/theorems/ffe4456c-b3b1-4fd1-b74e-561c5c40cd5e
-- title:
--   Embedded Resolution: is Radical bi Inf span singleton
-- statement:
--   The Embedded Resolution construction uses the is Radical bi Inf span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L60-L66

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.isRadical_biInf_span_singleton {R : Type*} [CommRing R] {ι : Type*}
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime) :
    (⨅ i ∈ s, Ideal.span ({f i} : Set R)).IsRadical := by sorry
