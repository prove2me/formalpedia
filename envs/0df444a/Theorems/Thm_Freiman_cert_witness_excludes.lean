-- Prove2me | Theorems.Thm_Freiman_cert_witness_excludes
-- name    : Freiman.cert_witness_excludes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:23.670002+00:00
-- url     : https://prove2.me/theorems/5cc5c33f-793c-40c4-b27d-b01e2d9a9467
-- title:
--   Certificate: witness excludes
-- statement:
--   Every valid exact certificate witness excludes its displayed pair of lower and upper q-premises at every point of its full closed rectangle. The conclusion is mathematical soundness of the finite record, not a claim that any history catalog is exhaustive.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_witness_excludes :
    ∀ (w : CertWitness), certWitnessValid w → ∀ r s q : ℝ, certRectangleMem w.rectangle r s → ¬ (certBoundHolds w.lowerBound r s q ∧ certBoundHolds w.upperBound r s q) := by
  sorry

end Freiman
