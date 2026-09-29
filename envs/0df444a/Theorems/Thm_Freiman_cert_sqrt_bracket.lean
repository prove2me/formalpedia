-- Prove2me | Theorems.Thm_Freiman_cert_sqrt_bracket
-- name    : Freiman.cert_sqrt_bracket
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:38.154033+00:00
-- url     : https://prove2.me/theorems/fe8ed298-e853-4116-8e82-7fda13634f4a
-- title:
--   Certificate: sqrt bracket
-- statement:
--   Strict rational enclosures of a positive square root follow from the two integer-square comparisons and nonnegative enclosure endpoints.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_sqrt_bracket :
    ∀ n l u : ℝ, 0 ≤ l → 0 ≤ u → l^2 < n → n < u^2 → l < Real.sqrt n ∧ Real.sqrt n < u := by
  sorry

end Freiman
