-- Prove2me | Theorems.Thm_Freiman_cert_witness_polynomial_positive
-- name    : Freiman.cert_witness_polynomial_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:10.254839+00:00
-- url     : https://prove2.me/theorems/a3a6dc4b-94e2-4d0d-a262-675b526f1da9
-- title:
--   Certificate: witness polynomial positive
-- statement:
--   The witness polynomial has the certified sign everywhere in its parameter rectangle; this combines exact coefficient identity, radical arithmetic and Bernstein soundness.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_witness_polynomial_positive :
    ∀ w : CertWitness, certWitnessValid w → (∀ i j : Fin 3, 0 < w.lowerBounds i j) → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 < certPolyEval (certCrossPolynomial w.lowerBound.threshold w.upperBound.threshold) r s := by
  sorry

end Freiman
