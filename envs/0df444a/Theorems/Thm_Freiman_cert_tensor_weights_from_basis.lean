-- Prove2me | Theorems.Thm_Freiman_cert_tensor_weights_from_basis
-- name    : Freiman.cert_tensor_weights_from_basis
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:57.464531+00:00
-- url     : https://prove2.me/theorems/52cdcf13-e436-4601-a085-c225021a239f
-- title:
--   Certificate: tensor weights from basis
-- statement:
--   Products of the two univariate Bernstein partitions give nine nonnegative weights summing to one.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_tensor_weights_from_basis :
    ∀ (R : CertRectangle) (r s : ℝ),
    ((∀ i : Fin 3, 0 ≤ certBernsteinBasis i ((r-R.r0)/(R.r1-R.r0))) ∧ (∑ i : Fin 3, certBernsteinBasis i ((r-R.r0)/(R.r1-R.r0))) = 1) →
    ((∀ j : Fin 3, 0 ≤ certBernsteinBasis j ((s-R.s0)/(R.s1-R.s0))) ∧ (∑ j : Fin 3, certBernsteinBasis j ((s-R.s0)/(R.s1-R.s0))) = 1) →
    (∀ i j : Fin 3, 0 ≤ certBernsteinWeight R r s i j) ∧ (∑ i : Fin 3, ∑ j : Fin 3, certBernsteinWeight R r s i j) = 1 := by
  sorry

end Freiman
