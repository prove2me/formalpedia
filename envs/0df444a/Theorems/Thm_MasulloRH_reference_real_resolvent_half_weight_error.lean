-- Prove2me | Theorems.Thm_MasulloRH_reference_real_resolvent_half_weight_error
-- name    : MasulloRH.reference_real_resolvent_half_weight_error
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:38:33.878173+00:00
-- url     : https://prove2.me/theorems/1d079032-e2b5-4302-b0da-cc14e1f2c9f0
-- title:
--   Second-order error for the reference resolvent weight
-- statement:
--   For each trace-strip zero, the real reference resolvent falls below half its decay weight by at most sixteen times that weight divided by one plus the squared ordinate.
-- source:
--   Original derivation from the two reference resolvent denominators.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH

namespace MasulloRH
theorem reference_real_resolvent_half_weight_error (z : ZetaZerosInTraceStrip (1/2)) :
    0 ≤ zeroDecayWeight (1/2) z / 2 - (zeroResolventTerm (1/2) 3 z).re ∧
    (1 + z.val.im^2) * (zeroDecayWeight (1/2) z / 2 - (zeroResolventTerm (1/2) 3 z).re)
      ≤ 16 * zeroDecayWeight (1/2) z := by sorry
end MasulloRH
