-- Prove2me | Theorems.Thm_Multihoming_Hump_deriv_price_factor
-- name    : Multihoming.Hump.deriv_price_factor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:48.32692+00:00
-- url     : https://prove2.me/theorems/7e6ab319-2ce2-4eba-a2fa-727133b6775d
-- title:
--   Appendix A1, PDF p. 29 (printed p. 23) — dpᴹ/dμ = (2t + √(t(2t+e)) − μ)(2t − √(t(2t+e)) − μ)/(2t − μ)²
-- statement:
--   Let $t>0$, $e\ge0$ and $\mu<2t$. The symmetric price $p^M(\mu)=(t-\mu)(\mu+e)/(2t-\mu)$ of (26), as a function of $\mu$, is differentiable at $\mu$ with
--   $$\frac{dp^M}{d\mu}=\frac{\left(2t+\sqrt{t(2t+e)}-\mu\right)\left(2t-\sqrt{t(2t+e)}-\mu\right)}{(2t-\mu)^2}.$$
--
--   The factorization reduces the sign of $dp^M/d\mu$ to that of $2t-\sqrt{t(2t+e)}-\mu$, so the price peaks at $\mu=2t-\sqrt{t(2t+e)}$.
--
--   **Formalization Note** The derivative is two-sided (`HasDerivAt`). The hypotheses $t>0$, $e\ge0$ keep the square-root argument positive; $\mu<2t$ keeps the denominator nonzero.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 29 (printed p. 23), Appendix A1, display dpᴹ/dμ

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF p. 29:
dpᴹ/dμ = (2t + √(t(2t + e)) − μ)(2t − √(t(2t + e)) − μ)/(2t − μ)². -/
theorem deriv_price_factor (t e μ : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (hμ : μ < 2 * t) :
    HasDerivAt (fun x => Multihoming.Thresholds.pM t x e)
      ((2 * t + Real.sqrt (t * (2 * t + e)) - μ) * (2 * t - Real.sqrt (t * (2 * t + e)) - μ) /
        (2 * t - μ) ^ 2) μ := by sorry

end Multihoming.Hump
