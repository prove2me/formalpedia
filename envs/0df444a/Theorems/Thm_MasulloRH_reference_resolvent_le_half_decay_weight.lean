-- Prove2me | Theorems.Thm_MasulloRH_reference_resolvent_le_half_decay_weight
-- name    : MasulloRH.reference_resolvent_le_half_decay_weight
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:52:16.254649+00:00
-- url     : https://prove2.me/theorems/b65d1777-6dcc-455a-bce8-37144d946c69
-- title:
--   The reference resolvent costs at most half the zero-decay weight
-- statement:
--   For every zero in the full critical strip the norm of its reference resolvent at 3 is at most one half of its decay weight. Both resolvent denominators have squared norm at least one plus the ordinate squared.
-- source:
--   https://prove2.me/theorems/8a8241a3-d9c8-48c1-8ae5-d8b668fb1866

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH

namespace MasulloRH
theorem reference_resolvent_le_half_decay_weight (ρ : ZetaZerosInTraceStrip (1/2)) :
    ‖zeroResolventTerm (1/2) 3 ρ‖ ≤ zeroDecayWeight (1/2) ρ / 2 := by sorry
end MasulloRH
