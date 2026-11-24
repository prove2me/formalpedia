-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_span_singleton_prod_finset
-- name    : FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:29.859541+00:00
-- url     : https://prove2.me/theorems/d22ac660-3520-4f27-990d-7455261d3084
-- title:
--   Embedded Resolution: is Radical span singleton prod finset
-- statement:
--   The Embedded Resolution construction uses the is Radical span singleton prod finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L68-L75

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

theorem FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    (Ideal.span ({∏ i ∈ s, f i} : Set R)).IsRadical := by sorry
