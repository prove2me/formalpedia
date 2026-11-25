-- Prove2me | Theorems.Thm_IsOpenMap_mem_closure_singleton_of_apply
-- name    : IsOpenMap.mem_closure_singleton_of_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:44.326343+00:00
-- url     : https://prove2.me/theorems/633980a8-d7ba-4bf0-8089-fa1bf3e8188c
-- title:
--   Is Open Map: mem closure singleton of apply
-- statement:
--   The Is Open Map construction uses the mem closure singleton of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L5-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L5-L15

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsOpenMap

theorem IsOpenMap.mem_closure_singleton_of_apply {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hopen : IsOpenMap f) (hinj : Function.Injective f)
    {a b : A} (h : f b ∈ closure ({f a} : Set B)) : b ∈ closure ({a} : Set A) := by sorry
