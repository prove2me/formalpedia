-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_head_through_degree_51
-- name    : GrothendieckLB.Supplement.cq_head_through_degree_51
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T19:59:56.908111+00:00
-- url     : https://prove2.me/theorems/f33fb42f-833b-4f5c-9a55-00cabd3ebc7c
-- title:
--   Verified Taylor coefficient enclosures for the cubic–quintic scheme through degree 51
-- statement:
--   For the cubic–quintic correlation at the stated parameters, the linear Taylor coefficient is at least $88157382204959954858/10^{20}$. Each of the 25 nonlinear odd Taylor coefficients of degrees 3 through 51 satisfies its published rational upper bound in absolute value. The proof combines the exact integer calculation at cutoff 51 with the general soundness theorem for partial certificates.
-- source:
--   The cubic–quintic Grothendieck scheme of Saha et al., arXiv:2608.11158v2. Integer comparison theorem b094be9c-4c78-45b1-b1c5-ff13e214def1 and soundness theorem 1eef07d1-b84d-45a3-8451-3fa6b23fe4f1.

import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqHeadUnits

namespace GrothendieckLB.Supplement

theorem cq_head_through_degree_51 :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (88157382204959954858 : ℝ) / 10 ^ 20 ≤ GrothendieckLB.taylorCoeff 1 H ∧
      ∀ j : ℕ, j < 25 →
        |GrothendieckLB.taylorCoeff (2 * j + 3) H| ≤
          ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10 ^ 20 := by sorry

end GrothendieckLB.Supplement
