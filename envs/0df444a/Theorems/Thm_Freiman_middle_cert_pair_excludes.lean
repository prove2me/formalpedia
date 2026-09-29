-- Prove2me | Theorems.Thm_Freiman_middle_cert_pair_excludes
-- name    : Freiman.middle_cert_pair_excludes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:27:54.454346+00:00
-- url     : https://prove2.me/theorems/438672c4-8ab9-4cd4-8560-2d94e0998ff8
-- title:
--   Freiman M2B certificate: pair excludes
-- statement:
--   Every validated ordinary pair excludes its two actual q premises.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.middle_cert_pair_excludes :
    ∀ (C : MiddleCertCatalog) (p : MiddleCertPair), middleCertWitnessesValid C → middleCertPairValid C p 0 → ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → ¬ (certBoundHolds (middleCertBound C p.lowerBound) r s q ∧ certBoundHolds (middleCertBound C p.upperBound) r s q) := by
  sorry
