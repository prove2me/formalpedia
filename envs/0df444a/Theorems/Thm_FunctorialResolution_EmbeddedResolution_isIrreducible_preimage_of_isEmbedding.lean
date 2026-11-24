-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIrreducible_preimage_of_isEmbedding
-- name    : FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:57.64934+00:00
-- url     : https://prove2.me/theorems/a78c5ba7-abc9-4252-ac01-e3592672cc02
-- title:
--   Embedded Resolution: is Irreducible preimage of is Embedding
-- statement:
--   The Embedded Resolution construction uses the is Irreducible preimage of is Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L43-L54

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

theorem FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding {f : Y → X} (hf : Topology.IsEmbedding f)
    {T : Set X} (hT : IsIrreducible T) (hTr : T ⊆ Set.range f) :
    IsIrreducible (f ⁻¹' T) := by sorry
