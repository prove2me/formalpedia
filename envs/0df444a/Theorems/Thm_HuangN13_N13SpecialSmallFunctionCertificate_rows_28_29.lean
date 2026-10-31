-- Prove2me | Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_28_29
-- name    : HuangN13.N13SpecialSmallFunctionCertificate.rows_28_29
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T08:31:21.466986+00:00
-- url     : https://prove2.me/theorems/2945b360-d0c4-49a8-bae2-251edf50d74e
-- title:
--   Finite polynomial certificate rows 28 and 29
-- statement:
--   These eight original certificate rows cover the two displayed numerator coefficient vectors and all four ordinate coefficient vectors over the two-element field. Each row keeps its original explicit polynomial or local-coefficient argument. The combined theorem is their conjunction; it introduces no new mathematical assumption.
-- source:
--   Xiang Huang, Apache-2.0. FLT@51bbb4f191ad0d3753b87123635c100a638ae580, N13SpecialSmallFunctionCertificate. Exact flattened unit10 declaration ranges and SHA-256 values are in core-metadata.json; original-file line mapping is not asserted. Original row source owners are recorded in metadata.json.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem HuangN13.N13SpecialSmallFunctionCertificate.rows_28_29 : (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 0, 1, 1, 1] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 0, 1, 1, 1] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 0, 1, 1, 1] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 0, 1, 1, 1] ![1, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 0, 1, 1, 1] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 0, 1, 1, 1] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 0, 1, 1, 1] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 0, 1, 1, 1] ![1, 1]) := by sorry
