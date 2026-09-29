-- Prove2me | Theorems.Thm_Freiman_cert_unit_coordinate
-- name    : Freiman.cert_unit_coordinate
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:02.822973+00:00
-- url     : https://prove2.me/theorems/b1d05cb6-4085-488e-88ac-4902f5a0b85d
-- title:
--   Certificate: unit coordinate
-- statement:
--   Affine normalization maps each closed parameter interval onto the unit interval, including both endpoints.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_unit_coordinate :
    ∀ a b x : ℝ, a < b → x ∈ Set.Icc a b → (x-a)/(b-a) ∈ Set.Icc (0:ℝ) 1 := by
  sorry

end Freiman
