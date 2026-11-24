-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etale_surjective_affine_cover_baseChange
-- name    : FunctorialResolution.EmbeddedResolution.exists_etale_surjective_affine_cover_baseChange
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:46.682616+00:00
-- url     : https://prove2.me/theorems/c7cf5f31-7be1-40e6-bb78-bf2ac8f2b5d3
-- title:
--   Embedded Resolution: exists etale surjective affine cover base Change
-- statement:
--   The Embedded Resolution construction uses the exists etale surjective affine cover base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean#L153-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean#L153-L181

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

theorem FunctorialResolution.EmbeddedResolution.exists_etale_surjective_affine_cover_baseChange (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (K : Type u) [Field K] [Algebra k K] [IsReduced (baseChange f K)] :
    ∃ (W : Scheme.{u}) (c : W ⟶ X) (g : baseChange (c ≫ f) K ⟶ baseChange f K),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType (c ≫ f) ∧ QuasiCompact (c ≫ f) ∧
        Etale c ∧ Surjective c ∧
        IsAffine (baseChange (c ≫ f) K) ∧ IsReduced (baseChange (c ≫ f) K) ∧
        LocallyOfFiniteType (baseChangeToSpec (c ≫ f) K) ∧
        QuasiCompact (baseChangeToSpec (c ≫ f) K) ∧
        Etale g ∧ Surjective g ∧
        g ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K ∧
        g ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c := by sorry
