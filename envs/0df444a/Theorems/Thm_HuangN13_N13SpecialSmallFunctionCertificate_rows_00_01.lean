-- Prove2me | Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_00_01
-- name    : HuangN13.N13SpecialSmallFunctionCertificate.rows_00_01
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:09:48.755294+00:00
-- url     : https://prove2.me/theorems/625a456e-89f3-40dd-848c-81f0b5593751
-- title:
--   Finite polynomial certificate rows 0 and 1
-- statement:
--   These eight original certificate rows cover the two displayed numerator coefficient vectors and all four ordinate coefficient vectors over the two-element field. Each row keeps its original explicit polynomial or local-coefficient argument. The combined theorem is their conjunction; it introduces no new mathematical assumption.
-- source:
--   Xiang Huang, Apache-2.0. Original source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13SpecialSmallFunctionCertificate.lean; exact flattened source declaration ranges and hashes are recorded alongside this payload. Original-file line mapping is not asserted. Exact row source owners are in metadata.json.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem HuangN13.N13SpecialSmallFunctionCertificate.rows_00_01 : (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 0, 0, 0, 0] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 0, 0, 0, 0] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 0, 0, 0, 0] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 0, 0, 0, 0] ![1, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 0, 0, 0, 0] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 0, 0, 0, 0] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 0, 0, 0, 0] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 0, 0, 0, 0] ![1, 1]) := by sorry
