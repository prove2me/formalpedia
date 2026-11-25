-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_listProd_map_range_eq_prod
-- name    : FunctorialResolution.EmbeddedResolution.listProd_map_range_eq_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:42.454827+00:00
-- url     : https://prove2.me/theorems/5dbd9925-649e-58eb-aaae-b8e00952c240
-- title:
--   Embedded Resolution: list Prod map range eq prod
-- statement:
--   The Embedded Resolution construction uses the list Prod map range eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L39-L45

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.listProd_map_range_eq_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (List.map f (List.range m)).prod = ∏ j ∈ Finset.range m, f j := by sorry
