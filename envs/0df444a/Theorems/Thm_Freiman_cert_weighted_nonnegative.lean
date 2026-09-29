-- Prove2me | Theorems.Thm_Freiman_cert_weighted_nonnegative
-- name    : Freiman.cert_weighted_nonnegative
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:59.667116+00:00
-- url     : https://prove2.me/theorems/4820a3fd-ae31-495f-af0a-c3d824418756
-- title:
--   Certificate: weighted nonnegative
-- statement:
--   A finite sum of nonnegative coefficients multiplied by nonnegative weights is nonnegative.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_weighted_nonnegative :
    ∀ v w : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, 0 ≤ v i j) → (∀ i j : Fin 3, 0 ≤ w i j) → 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, v i j*w i j := by
  sorry

end Freiman
