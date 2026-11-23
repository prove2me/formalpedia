-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_head_coefficient_enclosures
-- name    : GrothendieckLB.Supplement.cq_head_coefficient_enclosures
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T16:36:07.105314+00:00
-- url     : https://prove2.me/theorems/1affdd31-aa38-4623-a872-ea9c2d721a4f
-- title:
--   Finite Hermite coefficient enclosures for the cubic–quintic scheme
-- statement:
--   Let $b_m$ be the Taylor coefficients of the cubic–quintic correlation with $(\eta,s_3,s_5)=(0.136419125,0.34101124,0.05276111)$. Then
--   $$
--   b_1\ge \frac{88157382204959954858}{10^{20}},\qquad
--   |b_{2j+3}|\le\frac{u_j}{10^{20}}\quad(0\le j<125).
--   $$
--   Here $u_j$ is the upward-rounded integer endpoint of the published interval for $|b_{2j+3}|$. These finite enclosures come from the Hermite coefficient formula and one-dimensional Gaussian integration in Appendix C.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, https://arxiv.org/pdf/2608.11158v2, Theorem 5.1 and equations (13)–(16), pp. 17–18, and Proposition 6.3, equation (27), p. 21. The individual interval midpoints and radii are in the b1 and b_head fields of https://github.com/trishullab/grothendieck-bounds/blob/17de8e2331859d37322c199a3d56fb81d740764f/upper-bounds/theorem-cubic-quintic/certificate.json

import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqHeadUnits

namespace GrothendieckLB.Supplement

theorem cq_head_coefficient_enclosures :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (88157382204959954858 : ℝ) / 10 ^ 20 ≤ GrothendieckLB.taylorCoeff 1 H ∧
      ∀ j : ℕ, j < 125 →
        |GrothendieckLB.taylorCoeff (2 * j + 3) H| ≤
          ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10 ^ 20 := by sorry

end GrothendieckLB.Supplement
