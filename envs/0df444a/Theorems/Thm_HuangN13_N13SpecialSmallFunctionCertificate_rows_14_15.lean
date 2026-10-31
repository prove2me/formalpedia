-- Prove2me | Theorems.Thm_HuangN13_N13SpecialSmallFunctionCertificate_rows_14_15
-- name    : HuangN13.N13SpecialSmallFunctionCertificate.rows_14_15
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T08:00:45.245464+00:00
-- url     : https://prove2.me/theorems/6501b646-fd27-4643-b1b5-fad17c632753
-- title:
--   Finite polynomial certificate rows 14 and 15
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

theorem HuangN13.N13SpecialSmallFunctionCertificate.rows_14_15 : (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 1, 0] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 1, 0] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 1, 0] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![0, 1, 1, 1, 0] ![1, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 1, 0] ![0, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 1, 0] ![1, 0]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 1, 0] ![0, 1]) ∧ (
  MazurProof.N13SpecialSmallFunctionCertificate.PairCertificate ![1, 1, 1, 1, 0] ![1, 1]) := by sorry
