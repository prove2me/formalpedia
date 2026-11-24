-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isClosed_sUnion_of_subset_irreducibleComponents
-- name    : FunctorialResolution.EmbeddedResolution.isClosed_sUnion_of_subset_irreducibleComponents
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:39.016182+00:00
-- url     : https://prove2.me/theorems/f15a310b-d99e-468f-8faf-b70fca3cb0fa
-- title:
--   Embedded Resolution: is Closed s Union of subset irreducible Components
-- statement:
--   The Embedded Resolution construction uses the is Closed s Union of subset irreducible Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/IrreducibleComponents.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/IrreducibleComponents.lean#L7-L14

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_IrreducibleComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open Set TopologicalSpace

theorem FunctorialResolution.EmbeddedResolution.isClosed_sUnion_of_subset_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsClosed (⋃₀ 𝒜) := by sorry
