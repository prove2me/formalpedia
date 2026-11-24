-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc
-- name    : FunctorialResolution.EmbeddedResolution.comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:47:05.074314+00:00
-- url     : https://prove2.me/theorems/7e2c75ba-1076-453b-92fc-8198e73c364f
-- title:
--   Embedded Resolution: comp fst comp eq comp snd comp sigma Opens Desc
-- statement:
--   The Embedded Resolution construction uses the comp fst comp eq comp snd comp sigma Opens Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L161-L166

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

theorem FunctorialResolution.EmbeddedResolution.comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens) (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) :
    r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ g' =
      r ≫ pullback.snd g' (sigmaOpensDesc Y U) ≫ sigmaOpensDesc Y U := by sorry
