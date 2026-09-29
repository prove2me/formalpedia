-- Prove2me | Theorems.Thm_Freiman_section14_record_from_pair
-- name    : Freiman.section14_record_from_pair
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:51:06.460416+00:00
-- url     : https://prove2.me/theorems/f459ce31-407e-4ed6-8c81-e543b3b8b353
-- title:
--   Freiman §14: section14 record from pair
-- statement:
--   Generic record semantics: its two cited premises contradict the shared Bernstein witness on an enclosing rectangle. This is a finite-list/index and interval-containment argument; its numerical input is exactly cert_witness_excludes.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.section14_record_from_pair (hw : ∀ w : CertWitness, certWitnessValid w → ∀ r s q : ℝ, certRectangleMem w.rectangle r s → ¬ (certBoundHolds w.lowerBound r s q ∧ certBoundHolds w.upperBound r s q)) : ∀ (C : Section14Catalog) (si : ℕ) (rec : Section14Record), section14RecordValid C si rec → section14RecordSound C si rec := by
  sorry
