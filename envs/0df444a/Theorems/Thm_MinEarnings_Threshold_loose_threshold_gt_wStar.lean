-- Prove2me | Theorems.Thm_MinEarnings_Threshold_loose_threshold_gt_wStar
-- name    : MinEarnings.Threshold.loose_threshold_gt_wStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:23.779152+00:00
-- url     : https://prove2.me/theorems/f8a14219-4cf2-4f57-8137-970573db3e2b
-- title:
--   Online Appendix p. 4 — loose-supply threshold exceeds the crossing wage
-- statement:
--   Under the regularity assumptions, if the revenue-maximizing price $p^*$ exceeds the demand–supply crossing $w^*$, then inverse cost at maximal revenue exceeds that crossing:
--
--   $$p^*>w^*\Longrightarrow H(R(p^*))>w^*.$$
--
--   This separates the loose-supply threshold from the tight-supply threshold in Theorem 1.
--
--   **Formalization Note** The statement is the inequality used in the second paragraph of the converse proof; $H$ is characterized only on positive expenditures, and the standing assumptions ensure $R(p^*)>0$.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix p. 4 (PDF 32), proof of Theorem 1, second paragraph

import Mathlib
import Definitions.Def_MinEarnings_Threshold_Setting

namespace MinEarnings.Threshold

theorem loose_threshold_gt_wStar (D S H : ℝ → ℝ) (pStar wStar : ℝ)
    (hA : Assumptions D S pStar wStar) (hH : IsCostInverse S H)
    (hloose : wStar < pStar) :
    wStar < H (revenue D pStar) := by sorry

end MinEarnings.Threshold
