-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_oaA1_max_before
-- name    : GDPRPrivacy.PriceRise.oaA1_max_before
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:30.087007+00:00
-- url     : https://prove2.me/theorems/e0d14c5b-b46a-453f-8e08-32422de27c89
-- title:
--   OA §A.1, OA p. 2 — before the GDPR, Π̂ is maximized exactly at p̂_h2 = (1+x−2α)/3 if α < α₁(x) and at p̂_l2 = (2(x−1)−α+β)/3 otherwise
-- statement:
--   Let $0 < x < 1$ and $\alpha \ge 0$, and let $\widehat\Pi(\hat p) = (\hat p + \alpha)\widehat D(\hat p)$ be the firm's profit before the GDPR, as a function of the price $\hat p \in \mathbb{R}$. Write $\alpha_1(x) = \max\{(1-2x)/2, 0\}$ and $\beta = \sqrt{6 + (x + \alpha - 1)^2}$. Then a price $\hat p$ maximizes $\widehat\Pi$ over all of $\mathbb{R}$ if and only if
--   $$\hat p = \begin{cases} \hat p_{h2} = \dfrac{1 + x - 2\alpha}{3} & \text{if } \alpha < \alpha_1(x),\\[2mm] \hat p_{l2} = \dfrac{2(x-1) - \alpha + \beta}{3} & \text{if } \alpha \ge \alpha_1(x). \end{cases}$$
--   In particular the maximizer exists and is unique.
--
--   This is the equilibrium price before the GDPR, $\hat p^\star$, in closed form; the paper's case 1a ($\hat p^\star > x$) and case 1b ($\hat p^\star \le x$) correspond to the two branches.
--
--   **Formalization Note** The "if" direction is the online appendix's summary ("$\widehat\Pi$ is maximized at …"); the "only if" direction is the uniqueness asserted in footnote 24, p. 11 ("$\hat p^\star$ is the unique extreme value that maximizes $\widehat\Pi$"). The maximization is over all real prices, not only over $[x-1, 1+x]$.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), OA pp. 1–2, §A.1 (summary sentence, OA p. 2); p. 31 (p̂⋆); p. 11, footnote 24 (uniqueness)

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem oaA1_max_before (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) (p : ℝ) :
    IsMaxOn (profitBefore x α) Set.univ p ↔
      p = (if α < alpha1 x then (1 + x - 2 * α) / 3
           else (2 * (x - 1) - α + beta x α) / 3) := by sorry

end GDPRPrivacy.PriceRise
