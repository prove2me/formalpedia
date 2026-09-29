-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirtyone_ge_two
-- name    : OddPerfectNumber.geom_ratio_lower_thirtyone_ge_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:46:52.576288+00:00
-- url     : https://prove2.me/theorems/636921f9-3db7-45d7-b155-3d9818550c02
-- title:
--   Cross-multiplied geometric lower bound for the 31-component
-- statement:
--   For every exponent e≥2, the local geometric sum for 31^e is at least 993/961 times 31^e, in integral cross-multiplied form.
-- source:
--   Exact telescoping and integer arithmetic for the 31-component abundance factor.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem geom_ratio_lower_thirtyone_ge_two (e : Nat) (he : 2 ≤ e) :
    993 * 31 ^ e ≤
      961 * (∑ i ∈ Finset.range (e + 1), 31 ^ i) := by
  sorry

end OddPerfectNumber
