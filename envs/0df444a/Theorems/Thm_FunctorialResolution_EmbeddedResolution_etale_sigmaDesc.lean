-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_etale_sigmaDesc
-- name    : FunctorialResolution.EmbeddedResolution.etale_sigmaDesc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:19.878607+00:00
-- url     : https://prove2.me/theorems/0bed23e7-c571-496b-908a-4cf667659b5a
-- title:
--   Embedded Resolution: etale sigma Desc
-- statement:
--   The Embedded Resolution construction uses the etale sigma Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L59-L62

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

theorem FunctorialResolution.EmbeddedResolution.etale_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Etale (f i)) : Etale (Sigma.desc f) := by sorry
