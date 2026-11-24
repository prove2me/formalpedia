-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_map_eq_map_comap_of_isPullback
-- name    : FunctorialResolution.EmbeddedResolution.comap_map_eq_map_comap_of_isPullback
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:56.561484+00:00
-- url     : https://prove2.me/theorems/e309b0ce-8c5a-4ab3-976d-8c1c4cd61685
-- title:
--   Embedded Resolution: comap map eq map comap of is Pullback
-- statement:
--   The Embedded Resolution construction uses the comap map eq map comap of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IdealSheafFlatDescent.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IdealSheafFlatDescent.lean#L16-L25

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

theorem FunctorialResolution.EmbeddedResolution.comap_map_eq_map_comap_of_isPullback {W X X' W' : Scheme.{u}} {f : W ⟶ X} {g : X' ⟶ X}
    {g' : W' ⟶ W} {f' : W' ⟶ X'} (H : IsPullback g' f' f g)
    [QuasiCompact f] [AlgebraicGeometry.Flat g] (I : W.IdealSheafData) :
    (I.map f).comap g = (I.comap g').map f' := by sorry
