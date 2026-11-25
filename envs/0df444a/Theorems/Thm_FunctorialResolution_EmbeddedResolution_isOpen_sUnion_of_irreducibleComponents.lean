-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isOpen_sUnion_of_irreducibleComponents
-- name    : FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_irreducibleComponents
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:36.566848+00:00
-- url     : https://prove2.me/theorems/c7915f46-0872-52cc-b6ee-0e560076a0f9
-- title:
--   Embedded Resolution: is Open s Union of irreducible Components
-- statement:
--   The Embedded Resolution construction uses the is Open s Union of irreducible Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L93-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L93-L117

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

theorem FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_irreducibleComponents {Z : Type*} [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Z] (C : Set (Set Z))
    (hdisj : ∀ S ∈ C, ∀ W ∈ irreducibleComponents Z, W ∉ C → Disjoint S W) :
    IsOpen (⋃₀ C) := by sorry
