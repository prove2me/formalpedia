-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_etale_comp_snd_pullback_sigmaOpensDesc
-- name    : FunctorialResolution.EmbeddedResolution.etale_comp_snd_pullback_sigmaOpensDesc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:43.507542+00:00
-- url     : https://prove2.me/theorems/959515d0-5bbb-4a36-8094-a3e054195e35
-- title:
--   Embedded Resolution: etale comp snd pullback sigma Opens Desc
-- statement:
--   The Embedded Resolution construction uses the etale comp snd pullback sigma Opens Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L137-L142

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

theorem FunctorialResolution.EmbeddedResolution.etale_comp_snd_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [Etale g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by sorry
