-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isAffine_baseChange_comp
-- name    : FunctorialResolution.EmbeddedResolution.isAffine_baseChange_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:50.857124+00:00
-- url     : https://prove2.me/theorems/2af2ea72-3f54-48d8-9c99-7949d89ade2a
-- title:
--   Embedded Resolution: is Affine base Change comp
-- statement:
--   The Embedded Resolution construction uses the is Affine base Change comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean#L78-L80

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_FieldExtensionEtaleCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
noncomputable section
variable {k : Type u} [Field k] {X W : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.isAffine_baseChange_comp (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange (c ≫ f) K) := by sorry
