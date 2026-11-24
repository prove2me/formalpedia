-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isAffine_sigmaOpens
-- name    : FunctorialResolution.EmbeddedResolution.isAffine_sigmaOpens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:58.100107+00:00
-- url     : https://prove2.me/theorems/43f20a39-c2df-4381-958f-210f30a2a0cc
-- title:
--   Embedded Resolution: is Affine sigma Opens
-- statement:
--   The Embedded Resolution construction uses the is Affine sigma Opens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L25-L28

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

theorem FunctorialResolution.EmbeddedResolution.isAffine_sigmaOpens (Y : Scheme.{u}) {ι : Type u} [Finite ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) : IsAffine (sigmaOpens Y U) := by sorry
