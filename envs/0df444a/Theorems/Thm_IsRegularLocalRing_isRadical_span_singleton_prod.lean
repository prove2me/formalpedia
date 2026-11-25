-- Prove2me | Theorems.Thm_IsRegularLocalRing_isRadical_span_singleton_prod
-- name    : IsRegularLocalRing.isRadical_span_singleton_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:22.74993+00:00
-- url     : https://prove2.me/theorems/2bd8acc4-d64f-47e6-a763-999c47357cd0
-- title:
--   Is Regular Local Ring: is Radical span singleton prod
-- statement:
--   The Is Regular Local Ring construction uses the is Radical span singleton prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/RegularLocalRing.lean#L451-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/RegularLocalRing.lean#L451-L460

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

theorem IsRegularLocalRing.isRadical_span_singleton_prod {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    [Fintype ι] (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R)) :
    (Ideal.span ({∏ i, x i} : Set R)).IsRadical := by sorry
