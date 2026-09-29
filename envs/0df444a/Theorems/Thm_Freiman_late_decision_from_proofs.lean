-- Prove2me | Theorems.Thm_Freiman_late_decision_from_proofs
-- name    : Freiman.late_decision_from_proofs
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:56:26.648381+00:00
-- url     : https://prove2.me/theorems/2446715e-77c9-4d8a-af3b-7b41a7bb70b5
-- title:
--   Freiman late: late decision from proofs
-- statement:
--   Structural induction on the finite decision tree: choose the true complementary q branch or a containing closed half-rectangle, exclude an empty node using its arithmetic proof, and establish every required route condition by its premise or contradiction after negation.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_decision_from_proofs (hc : ∀ (b : CertBound) (r s q : ℝ), certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q) : ∀ (C : LateCatalog), lateProofSound C → ∀ right3 bs R tr, lateDecisionValid C right3 bs R tr → lateDecisionSound C right3 bs R := by
  sorry
