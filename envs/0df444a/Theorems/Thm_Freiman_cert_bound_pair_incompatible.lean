-- Prove2me | Theorems.Thm_Freiman_cert_bound_pair_incompatible
-- name    : Freiman.cert_bound_pair_incompatible
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:15.243264+00:00
-- url     : https://prove2.me/theorems/5c797c91-1aa7-40e8-8178-981af9f23d28
-- title:
--   Certificate: bound pair incompatible
-- statement:
--   A lower q-bound and an upper q-bound contradict each other when their thresholds are strictly reversed, or weakly reversed with at least one strict q-inequality. All four strictness combinations are retained.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Definitions.Def_Freiman_certificates

open scoped BigOperators

namespace Freiman

theorem cert_bound_pair_incompatible :
    ∀ (l u : CertBound) (r s q : ℝ), l.lower=true → u.lower=false →
    (certThresholdVal u.threshold r s < certThresholdVal l.threshold r s ∨
      (certThresholdVal u.threshold r s ≤ certThresholdVal l.threshold r s ∧ (l.strict=true ∨ u.strict=true))) →
    ¬ (certBoundHolds l r s q ∧ certBoundHolds u r s q) := by
  sorry

end Freiman
