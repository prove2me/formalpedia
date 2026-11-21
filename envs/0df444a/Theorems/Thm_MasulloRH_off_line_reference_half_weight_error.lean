-- Prove2me | Theorems.Thm_MasulloRH_off_line_reference_half_weight_error
-- name    : MasulloRH.off_line_reference_half_weight_error
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:39:49.833477+00:00
-- url     : https://prove2.me/theorems/61906a7d-6f6f-46ea-b4b2-1044ba71e4e3
-- title:
--   Relative error in the total off-line reference mass
-- statement:
--   The real reference resolvent mass of zeros off the critical line differs from half their decay mass by at most 16/(1+99998²) times that mass.
-- source:
--   Original derivation from the two reference resolvent denominators.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH

namespace MasulloRH
theorem off_line_reference_half_weight_error :
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2}
    let W := ∑' z : Z, zeroDecayWeight (1/2) z.val
    let K := ∑' z : Z, (zeroResolventTerm (1/2) 3 z.val).re
    0 ≤ W/2-K ∧ (1+99998^2)*(W/2-K) ≤ 16*W := by sorry
end MasulloRH
