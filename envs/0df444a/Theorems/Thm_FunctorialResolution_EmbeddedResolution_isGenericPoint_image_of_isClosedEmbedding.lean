-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isGenericPoint_image_of_isClosedEmbedding
-- name    : FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:42.412967+00:00
-- url     : https://prove2.me/theorems/f96aae2e-091e-4589-8ad6-d80d7fea0ac3
-- title:
--   Embedded Resolution: is Generic Point image of is Closed Embedding
-- statement:
--   The Embedded Resolution construction uses the is Generic Point image of is Closed Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L64-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L64-L78

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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding {f : Y → X}
    (hf : Topology.IsClosedEmbedding f) {y : Y} {T : Set Y} (h : IsGenericPoint y T) :
    IsGenericPoint (f y) (f '' T) := by sorry
