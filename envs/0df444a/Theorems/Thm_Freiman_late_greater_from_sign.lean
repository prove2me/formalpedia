-- Prove2me | Theorems.Thm_Freiman_late_greater_from_sign
-- name    : Freiman.late_greater_from_sign
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:56:46.100709+00:00
-- url     : https://prove2.me/theorems/de09047c-7bee-4bd4-bfdf-eccb197ce6e7
-- title:
--   Freiman late: late greater from sign
-- statement:
--   One continuant-difference identity transfers the scalar threshold comparison to actual endpoint values, including strict comparisons. All four tails are nonnegative, so the omitted denominators are positive; an identical pair of tails cannot justify strictness.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_greater_from_sign (hsg : ∀ z : CertField, (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧ (0 < lowerHistorySign z ↔ 0 < certFieldVal z)) : lateGreaterLaw := by
  sorry
