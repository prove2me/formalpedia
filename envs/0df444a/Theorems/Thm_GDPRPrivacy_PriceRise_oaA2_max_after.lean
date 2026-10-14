-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_oaA2_max_after
-- name    : GDPRPrivacy.PriceRise.oaA2_max_after
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:12.167429+00:00
-- url     : https://prove2.me/theorems/91fe3658-ea6a-4bcb-98a4-5c435bb44f91
-- title:
--   OA §A.2, OA p. 4 — after the GDPR, Π̃ is maximized exactly at p̃_h = (2(1−xα)+x²)/4 if α < α₂(x) and at p̃_l2 = (Γ−(2−2x+α))/3 otherwise
-- statement:
--   Let $0 < x < 1$ and $\alpha \ge 0$, and let $\widetilde\Pi(\tilde p) = \tilde p\,\widetilde D(\tilde p) + \alpha\,\widetilde D_S(\tilde p)$ be the firm's profit after the GDPR, as a function of the price $\tilde p \in \mathbb{R}$. Write $\alpha_2(x) = \max\{(2 - 4x + x^2)/(2x), 0\}$ and $\Gamma = \sqrt{6 + (2 - 2x + \alpha)^2}$. Then a price $\tilde p$ maximizes $\widetilde\Pi$ over all of $\mathbb{R}$ if and only if
--   $$\tilde p = \begin{cases} \tilde p_{h} = \dfrac{2(1 - \alpha x) + x^2}{4} & \text{if } \alpha < \alpha_2(x),\\[2mm] \tilde p_{l2} = \dfrac{\Gamma - (2 - 2x + \alpha)}{3} & \text{if } \alpha \ge \alpha_2(x). \end{cases}$$
--   In particular the maximizer exists and is unique.
--
--   This is the equilibrium price after the GDPR, $\tilde p^\star$, in closed form (p. 32); the paper's case 2a ($\tilde p^\star > x$) and case 2b ($0 \le \tilde p^\star \le x$) correspond to the two branches.
--
--   **Formalization Note** The "only if" direction (uniqueness) is the post-GDPR counterpart of footnote 24 and of the paper's reference to "the" equilibrium price. The maximization is over all real prices; $\tilde p^\star \ge 0$ is a consequence, not an assumption.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), OA pp. 2–4, §A.2 (summary sentence, OA p. 4); p. 32 (p̃⋆)

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem oaA2_max_after (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) (p : ℝ) :
    IsMaxOn (profitAfter x α) Set.univ p ↔
      p = (if α < alpha2 x then (2 * (1 - α * x) + x ^ 2) / 4
           else (Gamma x α - (2 - 2 * x + α)) / 3) := by sorry

end GDPRPrivacy.PriceRise
