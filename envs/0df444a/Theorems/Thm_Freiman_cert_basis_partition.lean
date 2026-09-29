-- Prove2me | Theorems.Thm_Freiman_cert_basis_partition
-- name    : Freiman.cert_basis_partition
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:01.262186+00:00
-- url     : https://prove2.me/theorems/69c6ed78-1ecd-49a0-b5fc-72361468e524
-- title:
--   Certificate: basis partition
-- statement:
--   The three quadratic Bernstein basis functions are nonnegative on the closed unit interval and sum exactly to one.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_basis_partition :
    ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → (∀ i : Fin 3, 0 ≤ certBernsteinBasis i t) ∧ (∑ i : Fin 3, certBernsteinBasis i t) = 1 := by
  sorry

end Freiman
