-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mul_tunedIdeal_le_iff
-- name    : FunctorialResolution.EmbeddedResolution.mul_tunedIdeal_le_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:27.956798+00:00
-- url     : https://prove2.me/theorems/461e88af-cd8e-4a47-aefc-d26c63216a06
-- title:
--   Embedded Resolution: mul tuned Ideal le iff
-- statement:
--   The Embedded Resolution construction uses the mul tuned Ideal le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L357-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L357-L367

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
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

theorem FunctorialResolution.EmbeddedResolution.mul_tunedIdeal_le_iff (I J : Ideal S) (m s : ℕ) (K : Ideal S) :
    I * tunedIdeal k J m s ≤ K ↔
      ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → I * tuningMonomial k J m c ≤ K := by sorry
