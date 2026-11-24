-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_smooth_sigmaDesc
-- name    : FunctorialResolution.EmbeddedResolution.smooth_sigmaDesc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:07.3698+00:00
-- url     : https://prove2.me/theorems/afc12763-0014-4405-8dd3-63b199d7ad7b
-- title:
--   Embedded Resolution: smooth sigma Desc
-- statement:
--   The Embedded Resolution construction uses the smooth sigma Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L144-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L144-L146

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

theorem FunctorialResolution.EmbeddedResolution.smooth_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Smooth (f i)) : Smooth (Sigma.desc f) := by sorry
