-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_affine_etale_cover_of_isReduced
-- name    : FunctorialResolution.EmbeddedResolution.exists_affine_etale_cover_of_isReduced
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:57.466308+00:00
-- url     : https://prove2.me/theorems/ead6706a-cf66-4769-b10c-f75a59cbfa9a
-- title:
--   Embedded Resolution: exists affine etale cover of is Reduced
-- statement:
--   The Embedded Resolution construction uses the exists affine etale cover of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L116-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L116-L135

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
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

theorem FunctorialResolution.EmbeddedResolution.exists_affine_etale_cover_of_isReduced {k : Type u} [Field k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced Y] :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (g : W ⟶ Y),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType q ∧ QuasiCompact q ∧
        Etale g ∧ Surjective g ∧ g ≫ p = q := by sorry
