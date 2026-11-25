-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_finite_affine_cover_subordinate
-- name    : FunctorialResolution.EmbeddedResolution.exists_finite_affine_cover_subordinate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:43.86256+00:00
-- url     : https://prove2.me/theorems/de2b98d6-d452-4abd-8d00-996aaee2964a
-- title:
--   Embedded Resolution: exists finite affine cover subordinate
-- statement:
--   The Embedded Resolution construction uses the exists finite affine cover subordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SubordinateAffineCover.lean#L18-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SubordinateAffineCover.lean#L18-L50

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SubordinateAffineCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u

theorem FunctorialResolution.EmbeddedResolution.exists_finite_affine_cover_subordinate {X' X : Scheme.{u}} [CompactSpace X']
    (φ : X' ⟶ X) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    ∃ (κ : Type u) (_ : Finite κ) (V : κ → X'.Opens) (β : κ → ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) ∧ iSup V = ⊤ := by sorry
