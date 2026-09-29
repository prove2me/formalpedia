-- Prove2me | Theorems.Thm_Freiman_cert_weighted_positive
-- name    : Freiman.cert_weighted_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:09.891311+00:00
-- url     : https://prove2.me/theorems/d88c0695-293b-4147-936c-c578c10bd6fc
-- title:
--   Certificate: weighted positive
-- statement:
--   Strict positivity of every coefficient makes the weighted sum strictly positive when the nonnegative weights sum to one, including rectangle boundary points.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_weighted_positive :
    ∀ v w : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, 0 < v i j) → (∀ i j : Fin 3, 0 ≤ w i j) → (∑ i : Fin 3, ∑ j : Fin 3, w i j)=1 → 0 < ∑ i : Fin 3, ∑ j : Fin 3, v i j*w i j := by
  sorry

end Freiman
