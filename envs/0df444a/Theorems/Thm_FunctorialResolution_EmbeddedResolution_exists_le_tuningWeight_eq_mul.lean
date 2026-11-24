-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_le_tuningWeight_eq_mul
-- name    : FunctorialResolution.EmbeddedResolution.exists_le_tuningWeight_eq_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:02.480041+00:00
-- url     : https://prove2.me/theorems/28bf19ec-9057-4267-aa1f-9cc3dcf3870f
-- title:
--   Embedded Resolution: exists le tuning Weight eq mul
-- statement:
--   The Embedded Resolution construction uses the exists le tuning Weight eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdealPowers.lean#L24-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdealPowers.lean#L24-L119

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdealPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.exists_le_tuningWeight_eq_mul (m L r : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (c : ℕ → ℕ)
    (hc : r * L + (m - 1) * L ≤ tuningWeight m c) :
    ∃ c' : ℕ → ℕ, (∀ j, c' j ≤ c j) ∧ tuningWeight m c' = r * L := by sorry
