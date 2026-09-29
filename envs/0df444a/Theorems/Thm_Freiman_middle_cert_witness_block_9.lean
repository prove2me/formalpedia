-- Prove2me | Theorems.Thm_Freiman_middle_cert_witness_block_9
-- name    : Freiman.middle_cert_witness_block_9
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:27:46.949304+00:00
-- url     : https://prove2.me/theorems/7e8a346c-c1d5-42d6-a12b-4c2a6f3e81c2
-- title:
--   Freiman M2B certificate: witness block 9
-- statement:
--   Exact finite arithmetic validator for source witness IDs 1135–1260. Retain all coefficients, directions, threshold IDs and printed rational bounds; the two nonzero-direction witnesses use the separate diagonal validator.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.middle_cert_witness_block_9 :
    ∀ w ∈ middleCertWitnesses9, middleCertWitnessValid middleCertData w := by
  sorry
