-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_span_pow_mul_tuningMonomial_le
-- name    : FunctorialResolution.EmbeddedResolution.span_pow_mul_tuningMonomial_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:22.605891+00:00
-- url     : https://prove2.me/theorems/c04de142-a175-4783-a87f-9a687e3dcc63
-- title:
--   Embedded Resolution: span pow mul tuning Monomial le
-- statement:
--   The Embedded Resolution construction uses the span pow mul tuning Monomial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L369-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L369-L383

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

theorem FunctorialResolution.EmbeddedResolution.span_pow_mul_tuningMonomial_le (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (n : ℕ) (c : ℕ → ℕ) :
    Ideal.span {x ^ n} * tuningMonomial k J m c ≤ tunedIdeal k J m (tuningWeight m c + n) := by sorry
