-- Prove2me | Theorems.Thm_IsLocalization_map_eq_map_of_map_eq_map
-- name    : IsLocalization.map_eq_map_of_map_eq_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:29.100855+00:00
-- url     : https://prove2.me/theorems/2638e8d2-d94a-4da3-b6de-2904ef642cc2
-- title:
--   Is Localization: map eq map of map eq map
-- statement:
--   The Is Localization construction uses the map eq map of map eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L81-L96

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalization

theorem IsLocalization.map_eq_map_of_map_eq_map {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (M : Submonoid R) [IsLocalization M S]
    [IsLocalization M T] {I J : Ideal R}
    (h : Ideal.map (algebraMap R S) I = Ideal.map (algebraMap R S) J) :
    Ideal.map (algebraMap R T) I = Ideal.map (algebraMap R T) J := by sorry
