-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isAffine_baseChange
-- name    : FunctorialResolution.EmbeddedResolution.isAffine_baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:41.432029+00:00
-- url     : https://prove2.me/theorems/7e0ebe11-0fce-44d5-a9c4-dc060a513eb3
-- title:
--   Embedded Resolution: is Affine base Change
-- statement:
--   The Embedded Resolution construction uses the is Affine base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean#L71-L76

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

theorem FunctorialResolution.EmbeddedResolution.isAffine_baseChange (p : W ⟶ Spec (CommRingCat.of k)) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange p K) := by sorry
