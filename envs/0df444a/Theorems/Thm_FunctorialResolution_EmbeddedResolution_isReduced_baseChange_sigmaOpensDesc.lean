-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isReduced_baseChange_sigmaOpensDesc
-- name    : FunctorialResolution.EmbeddedResolution.isReduced_baseChange_sigmaOpensDesc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:40.47613+00:00
-- url     : https://prove2.me/theorems/55731116-4a5a-4836-8ae0-41b2b0f0aeef
-- title:
--   Embedded Resolution: is Reduced base Change sigma Opens Desc
-- statement:
--   The Embedded Resolution construction uses the is Reduced base Change sigma Opens Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean#L115-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/FieldExtensionEtaleCover.lean#L115-L151

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

theorem FunctorialResolution.EmbeddedResolution.isReduced_baseChange_sigmaOpensDesc (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] [IsReduced (baseChange f K)]
    {ι : Type u} (U : ι → X.Opens) :
    IsReduced (baseChange (sigmaOpensDesc X U ≫ f) K) := by sorry
