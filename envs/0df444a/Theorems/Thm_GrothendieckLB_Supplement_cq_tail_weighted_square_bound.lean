-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_tail_weighted_square_bound
-- name    : GrothendieckLB.Supplement.cq_tail_weighted_square_bound
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T16:35:28.73247+00:00
-- url     : https://prove2.me/theorems/a98d397b-1cb5-4836-8b3a-b6271cf7cabd
-- title:
--   Third-order coefficient energy of the cubic–quintic tail
-- statement:
--   For the cubic–quintic correlation with the paper's parameters, write $b_m$ for its Taylor coefficients. Every finite initial part of the odd tail satisfies
--   $$
--   \sum_{j=0}^{n-1}(253+2j)^6 b_{253+2j}^2\le 14.443^2.
--   $$
--   These are nonnegative terms in the Parseval expansion of $\|D^3H\|_{L^2(\mathbb T)}^2$, where $D=z\,d/dz$. The bound uses the boundary norm certified in Proposition 6.3.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, https://arxiv.org/pdf/2608.11158v2, equations (26)–(27), pp. 20–21, and Appendix C. The boundary-norm certificate is https://github.com/trishullab/grothendieck-bounds/blob/17de8e2331859d37322c199a3d56fb81d740764f/upper-bounds/theorem-cubic-quintic/d3h_certificate.json

import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr

namespace GrothendieckLB.Supplement

theorem cq_tail_weighted_square_bound :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    ∀ n : ℕ, (∑ j ∈ Finset.range n,
      ((251 : ℝ) + 2 * ((j : ℝ) + 1)) ^ 6 *
        (GrothendieckLB.taylorCoeff (2 * j + 253) H) ^ 2) ≤ (14.443 : ℝ) ^ 2 := by sorry

end GrothendieckLB.Supplement
