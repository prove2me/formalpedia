-- Prove2me | Theorems.Thm_LeveragedPayouts_Unregulated_bracket_neg
-- name    : LeveragedPayouts.Unregulated.bracket_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:19.913974+00:00
-- url     : https://prove2.me/theorems/1efe5c3e-347f-40e6-a794-58a7e0bdf609
-- title:
--   Appendix B, proof of Proposition 11, p. 56 — the bracket of (60) is negative at l_ρ when e < π
-- statement:
--   In the economy of the mission, let $l_\rho$ be the first-best date-0 labour for the shock $\rho$, $\pi f'(l_\rho)/(2R)=\rho g'(1-l_\rho)$, and let $e<\pi$. Then
--   $$\Big(e-\frac{e^2}{2\pi}\Big)\frac{f'(l_\rho)}{R}-\rho\,g'(1-l_\rho)<0 .$$
--
--   This is the sign of the bracket in (60), the marginal social value of labour at $l_\rho$ when effort is below its first-best level $\pi$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 56, Appendix B, proof of Proposition 11, after (60)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.Unregulated
theorem bracket_neg (E : Economy) (ρ lρ e : ℝ) (hlρ : IsFirstBestLabor E ρ lρ) (he : e < E.π) :
    (e - e ^ 2 / (2 * E.π)) * deriv E.f lρ / E.R - ρ * deriv E.g (1 - lρ) < 0 := by sorry
end LeveragedPayouts.Unregulated
