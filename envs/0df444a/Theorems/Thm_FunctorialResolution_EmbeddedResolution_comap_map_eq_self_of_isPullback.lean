-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_map_eq_self_of_isPullback
-- name    : FunctorialResolution.EmbeddedResolution.comap_map_eq_self_of_isPullback
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:47:03.272322+00:00
-- url     : https://prove2.me/theorems/d4fb7e0d-05cc-4099-87f7-91113259b843
-- title:
--   Embedded Resolution: comap map eq self of is Pullback
-- statement:
--   The Embedded Resolution construction uses the comap map eq self of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IdealSheafFlatDescent.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IdealSheafFlatDescent.lean#L27-L41

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatComapInjective
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.comap_map_eq_self_of_isPullback {W X Q : Scheme.{u}} (γ : W ⟶ X)
    [QuasiCompact γ] [AlgebraicGeometry.Flat γ] {p q : Q ⟶ W} (H : IsPullback p q γ γ)
    (I : W.IdealSheafData) (hI : I.comap p = I.comap q) :
    (I.map γ).comap γ = I := by sorry
