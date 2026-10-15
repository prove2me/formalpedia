-- Prove2me | Theorems.Thm_MinEarnings_Threshold_phi_gt_one
-- name    : MinEarnings.Threshold.phi_gt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:11.517976+00:00
-- url     : https://prove2.me/theorems/f25c93f9-3087-4a61-af67-18759e61ee3a
-- title:
--   Online Appendix p. 4 — wage-growth factor exceeds one above the crossing
-- statement:
--   In the tight-supply case $p^*\le w^*$, let $M>w^*$. The wage-growth factor defined in the proof of Theorem 1 satisfies
--
--   $$\phi(M)=\frac{M}{H(R(M))}>1.$$
--
--   This inequality gives the strict growth rate that conflicts with bounded wages above the stability threshold.
--
--   **Formalization Note** The page's stated reason for the strict inequality does not establish it; the claim itself follows from $R(M)<C(M)$ when $M>w^*$. The Lean statement retains the case assumption of the printed paragraph and asserts only the displayed conclusion.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix p. 4 (PDF 32), proof of Theorem 1, display defining φ(M)

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

namespace MinEarnings.Threshold

theorem phi_gt_one (D S H : ℝ → ℝ) (pStar wStar M : ℝ)
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (htight : pStar ≤ wStar) (hMw : wStar < M) :
    1 < M / H (revenue D M) := by sorry

end MinEarnings.Threshold
