-- Prove2me | Theorems.Thm_HuangN13_N13SpecialCertifiedNumerator_exists_certified_numerator
-- name    : HuangN13.N13SpecialCertifiedNumerator.exists_certified_numerator
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:45:59.820975+00:00
-- url     : https://prove2.me/theorems/b817b4d5-baa8-4c59-898b-ee6ed5709b59
-- title:
--   A coherent comparison has a certified six-branch numerator
-- statement:
--   Every coherent comparison of tensor charts of four degree-two special divisors admits nonzero coefficient data for a small numerator satisfying the original cross-multiplication identity, six first-nonzero-coefficient certificates below order nine, and zero weighted jet code.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; no original-file line mapping is asserted. Target flattened unit21 lines3036-3059, command SHA-256 55e21a5730f25f9c70c19c177c996904ba7145278bbaf658480c91946441ca1a.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SpecialJetCodeCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialCertifiedNumerator.exists_certified_numerator
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    ∃ (a : Fin 5 → MazurProof.N13SpecialSmallFunctionCertificate.K) (b : Fin 2 → MazurProof.N13SpecialSmallFunctionCertificate.K),
      MazurProof.N13SpecialAffineNorm.linear (MazurProof.N13SpecialSmallFunctionCertificate.numerator a) (MazurProof.N13SpecialSmallFunctionCertificate.ordinate b) ≠ 0 ∧
      h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) =
        h.aDen * MazurProof.N13SpecialAffineNorm.linear (MazurProof.N13SpecialSmallFunctionCertificate.numerator a) (MazurProof.N13SpecialSmallFunctionCertificate.ordinate b) ∧
      (∀ i : Fin 6, MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i < 9 ∧
        (MazurProof.N13SpecialSmallFunctionCertificate.sixJetPolynomials a b i).coeff (MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i) ≠ 0 ∧
        ∀ j : Fin 9, (j : ℕ) < MazurProof.N13SpecialSmallFunctionCertificate.sixJetOrders a b i → (MazurProof.N13SpecialSmallFunctionCertificate.sixJetPolynomials a b i).coeff j = 0) ∧
      MazurProof.N13SpecialSmallFunctionCertificate.weightedJetCode a b = 0 := by sorry
