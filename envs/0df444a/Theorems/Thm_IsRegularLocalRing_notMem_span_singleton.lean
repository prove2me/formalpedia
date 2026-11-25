-- Prove2me | Theorems.Thm_IsRegularLocalRing_notMem_span_singleton
-- name    : IsRegularLocalRing.notMem_span_singleton
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:34.474492+00:00
-- url     : https://prove2.me/theorems/63633cba-ca89-444b-87f6-701786d1324f
-- title:
--   Is Regular Local Ring: not Mem span singleton
-- statement:
--   The Is Regular Local Ring construction uses the not Mem span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/RegularLocalRing.lean#L429-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/RegularLocalRing.lean#L429-L449

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

theorem IsRegularLocalRing.notMem_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    {i j : ι} (hij : i ≠ j) : x j ∉ Ideal.span ({x i} : Set R) := by sorry
