-- Prove2me | Theorems.Thm_HuangN13_N13SpecialSmallNumerator_exists_small_supported_numerator
-- name    : HuangN13.N13SpecialSmallNumerator.exists_small_supported_numerator
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:24:47.782911+00:00
-- url     : https://prove2.me/theorems/c10ccd4d-9ac4-41fe-84d4-a71330b52751
-- title:
--   A special coherent comparison has a small numerator with supported norm
-- statement:
--   Every coherent comparison between the tensor charts of four degree-two special divisors admits a nonzero numerator p+q·y with degree(p)≤4 and degree(q)≤1, the original cross-multiplication identity, and nonzero norm dividing X^i(X−1)^j for i+j≤16.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof; exact source-owner ranges and hashes are recorded in metadata.json. This is only the exact SpecialComparison/ofDivisor/tensor/tensorPolynomial statement closure. Exact target flattened unit10 lines8534-8562, command SHA-256 053d44611b8d82b94ffb11efacfdbde4e31d80225b9cf6ea4c540e180eb8e2a7.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialSmallNumerator.exists_small_supported_numerator
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    ∃ p q : MazurProof.N13SpecialDivisorCharts.K[X], ∃ i j : ℕ,
      p.natDegree ≤ 4 ∧ q.natDegree ≤ 1 ∧ i + j ≤ 16 ∧
      MazurProof.N13SpecialAffineNorm.linear p q ≠ 0 ∧
      h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) =
        h.aDen * MazurProof.N13SpecialAffineNorm.linear p q ∧
      MazurProof.N13SpecialAffineNorm.normPolynomial p q ≠ 0 ∧
      MazurProof.N13SpecialAffineNorm.normPolynomial p q ∣ X ^ i * (X - 1) ^ j := by sorry
