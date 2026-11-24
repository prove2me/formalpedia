-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_mul_left
-- name    : FunctorialResolution.EmbeddedResolution.tuningWeight_mul_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:50:11.299695+00:00
-- url     : https://prove2.me/theorems/737983fe-38b7-4873-99d7-a5a065e072c6
-- title:
--   Embedded Resolution: tuning Weight mul left
-- statement:
--   The Embedded Resolution construction uses the tuning Weight mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L19-L21

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

theorem FunctorialResolution.EmbeddedResolution.tuningWeight_mul_left (m n : ℕ) (c : ℕ → ℕ) :
    tuningWeight m (fun j => n * c j) = n * tuningWeight m c := by sorry
