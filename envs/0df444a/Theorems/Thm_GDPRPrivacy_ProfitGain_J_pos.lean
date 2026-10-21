-- Prove2me | Theorems.Thm_GDPRPrivacy_ProfitGain_J_pos
-- name    : GDPRPrivacy.ProfitGain.J_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:34.497964+00:00
-- url     : https://prove2.me/theorems/6e94aa7b-4748-49e4-a32e-a7f4253eb891
-- title:
--   Online Appendix §F, OA p. 9, conclusion — J(x, α) > 0 for α < α₁(x) = (1 − 2x)/2 and x < 1/2
-- statement:
--   Let
--   $$
--   J(x,\alpha)=76+27x^4-96\alpha-32\alpha^2(3+\alpha)+12x^2(1+\alpha)(1+9\alpha)-\big(4x^3(8+27\alpha)+24x(4+4\alpha^2-\alpha)\big).
--   $$
--   Then $J(x,\alpha)>0$ for all real $x,\alpha$ with
--   $$
--   0<x<\tfrac12,\qquad 0\le\alpha<\alpha_1(x)=\tfrac{1-2x}{2}.
--   $$
--
--   $J$ is $432$ times the difference of the equilibrium profits after and before the GDPR in the region $\alpha<\alpha_1(x)$. Its positivity is the last step of the proof of Proposition A3.
--
--   **Formalization Note.** This is a pure polynomial inequality; it does not mention the model. For $x<1/2$, $\alpha_1(x)=(1-2x)/2$, which is written out explicitly as in the source. The standing assumptions $x>0$ and $\alpha\ge0$ are hypotheses. The source also states $J(x,\alpha_1(x))=(1-x)^2x(4+9x)/16$, which is the value of $J/432$, not of $J$. That sentence is not part of this statement.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), OA p. 9, §F (Proof of Proposition A3), concluding sentence

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.ProfitGain

/-- Online Appendix §F, conclusion (OA p. 9): the numerator
`J(x, α) = 76 + 27x⁴ - 96α - 32α²(3 + α) + 12x²(1 + α)(1 + 9α) - (4x³(8 + 27α) + 24x(4 + 4α² - α))`
of `Π̃⋆ - Π̂⋆` is positive for all `(x, α)` with `0 < x < 1/2` and `0 ≤ α < α₁(x) = (1 - 2x)/2`. -/
theorem J_pos (x α : ℝ) (hx0 : 0 < x) (hxhalf : x < 1 / 2) (hα : 0 ≤ α)
    (hα1 : α < (1 - 2 * x) / 2) :
    0 < 76 + 27 * x ^ 4 - 96 * α - 32 * α ^ 2 * (3 + α) + 12 * x ^ 2 * (1 + α) * (1 + 9 * α)
      - (4 * x ^ 3 * (8 + 27 * α) + 24 * x * (4 + 4 * α ^ 2 - α)) := by sorry

end GDPRPrivacy.ProfitGain
