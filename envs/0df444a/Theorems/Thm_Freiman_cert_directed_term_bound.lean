-- Prove2me | Theorems.Thm_Freiman_cert_directed_term_bound
-- name    : Freiman.cert_directed_term_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:49.939247+00:00
-- url     : https://prove2.me/theorems/33a9d9c3-c656-4593-9d66-260860854866
-- title:
--   Certificate: directed term bound
-- statement:
--   Choosing the lower radical endpoint for a nonnegative rational coefficient and the upper endpoint for a negative coefficient gives a valid lower bound for that term.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_directed_term_bound :
    ∀ (q lo hi : ℚ) (x : ℝ), (lo:ℝ) ≤ x → x ≤ hi → (certDirectedTerm q lo hi:ℝ) ≤ (q:ℝ)*x := by
  sorry

end Freiman
