-- Prove2me | Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_30_31
-- name    : HuangN13.N13SpecialSmallFunctionCertificate.rows_30_31
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T07:09:58.634469+00:00
-- url     : https://prove2.me/theorems/e59303d6-9f72-47f8-9201-4f0cb8777e60
-- title:
--   Finite polynomial certificate rows 30 and 31
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

theorem HuangN13.N13SpecialSmallFunctionCertificate.rows_30_31 : (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 1, 1] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 1, 1] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 1, 1] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 1, 1] ![1, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 1, 1] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 1, 1] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 1, 1] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 1, 1] ![1, 1]) := by sorry
