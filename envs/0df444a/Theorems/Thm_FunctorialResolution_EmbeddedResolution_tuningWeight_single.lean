-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_single
-- name    : FunctorialResolution.EmbeddedResolution.tuningWeight_single
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:50:10.013497+00:00
-- url     : https://prove2.me/theorems/dd83e755-d214-456f-ad6f-8d03f11fc249
-- title:
--   Embedded Resolution: tuning Weight single
-- statement:
--   The Embedded Resolution construction uses the tuning Weight single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L30-L37

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

theorem FunctorialResolution.EmbeddedResolution.tuningWeight_single (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningWeight m (Pi.single i 1) = m - i := by sorry
