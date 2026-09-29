-- Prove2me | Theorems.Thm_Freiman_middle_cert_family_equal_II_b_short_valid
-- name    : Freiman.middle_cert_family_equal_II_b_short_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:29:07.347916+00:00
-- url     : https://prove2.me/theorems/fd61414d-799f-4e0f-b94f-47d75fa06c83
-- title:
--   Freiman M2B certificate: family equal II b short valid
-- statement:
--   Finite validator for equal_II_b_short: every native target has its exact stored endpoint/hypothesis match; every grouped record binds its actual pair witnesses and premise conjunction; every nonautomatic branch is covered with all required parent indices.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.middle_cert_family_equal_II_b_short_valid :
    middleCertFamilyValid middleCertData 7 := by
  sorry
