-- Prove2me | Theorems.Thm_HuangN13_N13SpecialLaurentBranches_degree_four_polynomial_bounds
-- name    : HuangN13.N13SpecialLaurentBranches.degree_four_polynomial_bounds
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:07:55.697155+00:00
-- url     : https://prove2.me/theorems/859b6365-c06d-4e91-89e4-e3f9dd78e69b
-- title:
--   Two infinity pole bounds force numerator degree four and ordinate degree one
-- statement:
--   If p+q·y has pole order at most four at both Laurent branches of the fixed good characteristic-two curve, then p has degree at most four and q has degree at most one.
-- source:
--   Xiang Huang, Apache-2.0. Original source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13SpecialLaurentBranches.lean; exact original prerequisites, source-owner ranges and hashes are recorded alongside the payload. Original-file line mapping is not asserted. Exact target flattened unit10 lines8014-8022, command SHA-256 4a1ab81aec5b3d5b7b655a81dbc0aa36940b04024fd8b75066fe7b21de57dac3.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialLaurentBranches.degree_four_polynomial_bounds (p q : MazurProof.N13SpecialLaurentBranches.K[X])
    (hpoles : (-4 : ℤ) ≤ (MazurProof.N13SpecialLaurentBranches.plus (MazurProof.N13SpecialAffineNorm.linear p q)).order)
    (hmoles : (-4 : ℤ) ≤ (MazurProof.N13SpecialLaurentBranches.minus (MazurProof.N13SpecialAffineNorm.linear p q)).order) :
    p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 := by sorry
