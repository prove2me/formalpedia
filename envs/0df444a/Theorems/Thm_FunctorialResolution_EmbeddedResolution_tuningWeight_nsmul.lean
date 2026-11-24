-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_nsmul
-- name    : FunctorialResolution.EmbeddedResolution.tuningWeight_nsmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:50:04.084752+00:00
-- url     : https://prove2.me/theorems/638ecbdd-2abb-4e06-9e53-3329758cf6ce
-- title:
--   Embedded Resolution: tuning Weight nsmul
-- statement:
--   The Embedded Resolution construction uses the tuning Weight nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L23-L28

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

theorem FunctorialResolution.EmbeddedResolution.tuningWeight_nsmul (m n : ℕ) (c : ℕ → ℕ) :
    tuningWeight m (n • c) = n * tuningWeight m c := by sorry
