-- Prove2me | Theorems.Thm_Freiman_late_witnesses_0925_1110
-- name    : Freiman.late_witnesses_0925_1110
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:55:06.152203+00:00
-- url     : https://prove2.me/theorems/431622ba-396a-4f05-b220-b0c258340637
-- title:
--   Freiman late: late witnesses 0925 1110
-- statement:
--   Exact validation of source witnesses W926–W1110: all nine displayed rational Bernstein lower bounds, correct strictness, valid closed rectangle and positive denominator factors. Polynomial coefficients are defined by the original threshold pair and rectangle, and their equality with every printed source matrix is recorded in the transcription audit.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_witnesses_0925_1110 : lateWitnessBatch 925 1110 := by
  sorry
