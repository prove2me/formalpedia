-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_finite_affine_cover
-- name    : FunctorialResolution.EmbeddedResolution.exists_finite_affine_cover
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:27.76363+00:00
-- url     : https://prove2.me/theorems/6b8f69a1-98f5-4920-af63-212150e3753c
-- title:
--   Embedded Resolution: exists finite affine cover
-- statement:
--   The Embedded Resolution construction uses the exists finite affine cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L98-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L98-L110

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

theorem FunctorialResolution.EmbeddedResolution.exists_finite_affine_cover (Y : Scheme.{u}) [CompactSpace Y] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Y.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ := by sorry
