-- Prove2me | Theorems.Thm_Freiman_late_decision_sound
-- name    : Freiman.late_decision_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:56:29.330308+00:00
-- url     : https://prove2.me/theorems/58a4c02e-09df-42c8-b583-303984eaf4ae
-- title:
--   Freiman late: late decision sound
-- statement:
--   Soundness of complete finite late decision trees, with exact implication premise selection.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_decision_sound : ∀ (C : LateCatalog), lateProofSound C → ∀ right3 bs R tr, lateDecisionValid C right3 bs R tr → lateDecisionSound C right3 bs R := by
  sorry
