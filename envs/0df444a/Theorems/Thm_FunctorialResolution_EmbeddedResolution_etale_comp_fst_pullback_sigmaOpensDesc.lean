-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_etale_comp_fst_pullback_sigmaOpensDesc
-- name    : FunctorialResolution.EmbeddedResolution.etale_comp_fst_pullback_sigmaOpensDesc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:48.443391+00:00
-- url     : https://prove2.me/theorems/40ac8643-ac1e-447f-86aa-dfe58d4c5d71
-- title:
--   Embedded Resolution: etale comp fst pullback sigma Opens Desc
-- statement:
--   The Embedded Resolution construction uses the etale comp fst pullback sigma Opens Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L130-L135

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

theorem FunctorialResolution.EmbeddedResolution.etale_comp_fst_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by sorry
