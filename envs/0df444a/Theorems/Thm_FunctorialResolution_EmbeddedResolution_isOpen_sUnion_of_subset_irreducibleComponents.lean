-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isOpen_sUnion_of_subset_irreducibleComponents
-- name    : FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_subset_irreducibleComponents
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:36.657106+00:00
-- url     : https://prove2.me/theorems/8531fbf8-beb7-5edc-8dd7-1b19433b43d6
-- title:
--   Embedded Resolution: is Open s Union of subset irreducible Components
-- statement:
--   The Embedded Resolution construction uses the is Open s Union of subset irreducible Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/IrreducibleComponents.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/IrreducibleComponents.lean#L16-L38

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

theorem FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_subset_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X]
    (hsep : ∀ C₁ ∈ irreducibleComponents X, ∀ C₂ ∈ irreducibleComponents X,
      (C₁ ∩ C₂).Nonempty → C₁ = C₂)
    {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsOpen (⋃₀ 𝒜) := by sorry
