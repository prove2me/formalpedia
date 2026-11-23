-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_claim_C_2_5_numeric
-- name    : GrothendieckPD.Digits.claim_C_2_5_numeric
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:51.864672+00:00
-- url     : https://prove2.me/theorems/a4a7c84f-a284-4acf-8076-c9af58b68926
-- title:
--   Claim 5 of Lemma C.2: grouped arcsine-head numerical certificate
-- statement:
--   Let $A_i$ be the finite arcsine head through degree $681$ defined using $P_{i,+}$, and let $\lambda_i$ be the exact mixture weights from Table 1. The grouped interval-arithmetic certificate for Claim 5 asserts
--   $$\sum_{i=19}^{31}\lambda_i(1-A_i)
--    +\lambda_{17}(6.982\cdot10^{-54})
--    +\lambda_{18}(1.223\cdot10^{-13})
--    <2.623422117515\cdot10^{-6}.$$
--
--   The first sum is the weighted output of the finite evaluation displayed after Eq. (C.36); the last two terms are the exceptional upper bounds from Eq. (C.37). This is the numerical content used by the paper when it says that summing the 256-bit interval bounds with weights $\lambda_i$ gives Eq. (C.34). No additional decimal margin has been inserted.
--
--   **Formalization Note** The heads and weights are exact real expressions, so proving this child is a finite exact/numerical certificate task independent of the Gaussian Hermite analysis.
-- source:
--   Heilman–Jones–Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820, proof of Lemma C.2, Claim 5, finite evaluation following Eq. (C.36), p. 35, and final weighted sum using Eq. (C.37), p. 36, yielding Eq. (C.34). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_ArcsineTail

open GrothendieckPD.Digits

/-- The grouped 256-bit interval certificate described after Eq. (C.36), pp. 35--36:
weighted finite-head deficits for `i = 19, ..., 31`, together with the displayed
Cauchy upper bounds for `i = 17, 18`, satisfy the exact numerical bound (C.34). -/
theorem GrothendieckPD.Digits.claim_C_2_5_numeric :
    (∑ i ∈ Finset.Icc 19 31, lam i * (1 - arcsinHead i)) +
        lam 17 * (6.982e-54 : ℝ) + lam 18 * (1.223e-13 : ℝ) <
      (0.000002623422117515 : ℝ) := by sorry
