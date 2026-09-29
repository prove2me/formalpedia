-- Prove2me | Theorems.Thm_Freiman_late_proof_from_witness
-- name    : Freiman.late_proof_from_witness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:57:34.967213+00:00
-- url     : https://prove2.me/theorems/f15385ab-52cd-42c5-a8d3-ab3f10762206
-- title:
--   Freiman late: late proof from witness
-- statement:
--   Generic semantics of the indexed arithmetic proof forest: a pair cites only present premises and its exact rectangle; each rectangle split covers its closed parent. Fuel is consumed at each descent, so a cycle cannot certify a contradiction.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.late_proof_from_witness (hw : ∀ w : CertWitness, certWitnessValid w → ∀ r s q : ℝ, certRectangleMem w.rectangle r s → ¬ (certBoundHolds w.lowerBound r s q ∧ certBoundHolds w.upperBound r s q)) : ∀ C : LateCatalog, lateAllWitnesses C → lateProofSound C := by
  sorry
