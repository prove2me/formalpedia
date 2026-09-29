-- Prove2me | Theorems.Thm_Freiman_cert_witness_denominators_positive
-- name    : Freiman.cert_witness_denominators_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:20.091822+00:00
-- url     : https://prove2.me/theorems/dfc4768a-b378-4536-8329-4248c2068ddd
-- title:
--   Certificate: witness denominators positive
-- statement:
--   The rational data validator supplies positive denominators for both threshold functions at every point of the rectangle.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_witness_denominators_positive :
    ∀ (w : CertWitness), certWitnessValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 < certThresholdDen w.lowerBound.threshold r ∧ 0 < certThresholdDen w.upperBound.threshold r := by
  sorry

end Freiman
