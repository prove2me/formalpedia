-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_pow_fun_mul
-- name    : FunctorialResolution.EmbeddedResolution.tuningMonomial_pow_fun_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:50:16.865132+00:00
-- url     : https://prove2.me/theorems/c36bc007-b009-493b-8eb0-e655c61775c4
-- title:
--   Embedded Resolution: tuning Monomial pow fun mul
-- statement:
--   The Embedded Resolution construction uses the tuning Monomial pow fun mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L79-L82

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

theorem FunctorialResolution.EmbeddedResolution.tuningMonomial_pow_fun_mul (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (fun j => n * c j) := by sorry
