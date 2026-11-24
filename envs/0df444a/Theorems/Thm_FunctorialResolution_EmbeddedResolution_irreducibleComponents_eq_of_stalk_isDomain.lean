-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_irreducibleComponents_eq_of_stalk_isDomain
-- name    : FunctorialResolution.EmbeddedResolution.irreducibleComponents_eq_of_stalk_isDomain
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:43.68636+00:00
-- url     : https://prove2.me/theorems/d6c022c1-5418-4d9b-85fc-8ef8c2f27d27
-- title:
--   Embedded Resolution: irreducible Components eq of stalk is Domain
-- statement:
--   The Embedded Resolution construction uses the irreducible Components eq of stalk is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/IrreducibleComponents.lean#L40-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/IrreducibleComponents.lean#L40-L72

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

theorem FunctorialResolution.EmbeddedResolution.irreducibleComponents_eq_of_stalk_isDomain (X : AlgebraicGeometry.Scheme)
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) {C₁ C₂ : Set X}
    (h₁ : C₁ ∈ irreducibleComponents X) (h₂ : C₂ ∈ irreducibleComponents X)
    {x : X} (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) : C₁ = C₂ := by sorry
