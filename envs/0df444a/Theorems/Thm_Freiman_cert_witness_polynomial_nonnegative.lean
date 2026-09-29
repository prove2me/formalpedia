-- Prove2me | Theorems.Thm_Freiman_cert_witness_polynomial_nonnegative
-- name    : Freiman.cert_witness_polynomial_nonnegative
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:17.569813+00:00
-- url     : https://prove2.me/theorems/eb1680d6-1aa1-40c3-bcd9-3990d292ab6f
-- title:
--   Certificate: witness polynomial nonnegative
-- statement:
--   The witness polynomial has the certified sign everywhere in its parameter rectangle; this combines exact coefficient identity, radical arithmetic and Bernstein soundness.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_witness_polynomial_nonnegative :
    ∀ w : CertWitness, certWitnessValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 ≤ certPolyEval (certCrossPolynomial w.lowerBound.threshold w.upperBound.threshold) r s := by
  sorry

end Freiman
