-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_span_singleton_prod_eq_biInf
-- name    : FunctorialResolution.EmbeddedResolution.span_singleton_prod_eq_biInf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:29.375185+00:00
-- url     : https://prove2.me/theorems/72123b98-f8b9-4131-bf26-fa85469181ed
-- title:
--   Embedded Resolution: span singleton prod eq bi Inf
-- statement:
--   The Embedded Resolution construction uses the span singleton prod eq bi Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L37-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L37-L58

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

theorem FunctorialResolution.EmbeddedResolution.span_singleton_prod_eq_biInf {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    Ideal.span ({∏ i ∈ s, f i} : Set R) = ⨅ i ∈ s, Ideal.span ({f i} : Set R) := by sorry
