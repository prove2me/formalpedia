-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_surjective_comp_fst_pullback_sigmaOpensDesc
-- name    : FunctorialResolution.EmbeddedResolution.surjective_comp_fst_pullback_sigmaOpensDesc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:08.441836+00:00
-- url     : https://prove2.me/theorems/97adcf40-f98e-4c74-a584-f602eee73f01
-- title:
--   Embedded Resolution: surjective comp fst pullback sigma Opens Desc
-- statement:
--   The Embedded Resolution construction uses the surjective comp fst pullback sigma Opens Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L144-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L144-L151

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpensPullback
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

theorem FunctorialResolution.EmbeddedResolution.surjective_comp_fst_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by sorry
