-- Prove2me | Theorems.Thm_Freiman_middle_cert_proof_from_pair_diagonal
-- name    : Freiman.middle_cert_proof_from_pair_diagonal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:19.432446+00:00
-- url     : https://prove2.me/theorems/2a654758-0426-4811-bc4d-80c86c8bdfc7
-- title:
--   Freiman M2B certificate: proof from pair diagonal
-- statement:
--   The two supported proof types are an ordinary bound pair or two diagonal pairs. For the diagonal proof choose s≤r or r≤s and use the actual strict L/U premise; no bisection or unrepresented proof shape is allowed.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.middle_cert_proof_from_pair_diagonal :
    (∀ (C : MiddleCertCatalog) (p : MiddleCertPair), middleCertWitnessesValid C → middleCertPairValid C p 0 → ∀ r s q : ℝ, certRectangleMem middleCertRectangle r s → ¬ (certBoundHolds (middleCertBound C p.lowerBound) r s q ∧ certBoundHolds (middleCertBound C p.upperBound) r s q)) → (∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → certDiagonalSide w r s → certThresholdVal w.upperThreshold r s ≤ certThresholdVal w.lowerThreshold r s) → ∀ (C : MiddleCertCatalog) (p : MiddleCertProof), middleCertWitnessesValid C → middleCertProofValid C p → middleCertProofSound C p := by
  sorry
