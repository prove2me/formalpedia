-- Prove2me | Theorems.Thm_Multihoming_Hump_deriv_profit_pos_at_zero
-- name    : Multihoming.Hump.deriv_profit_pos_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:38.249207+00:00
-- url     : https://prove2.me/theorems/be8d2b5e-212f-4cca-bf0a-0ac2218de8ef
-- title:
--   Appendix A1, PDF p. 28 (printed p. 22) — dπᴹ/dμ at μ = 0 is positive
-- statement:
--   Let $t>0$ and $0<e<2t$. The symmetric profit $\pi^M(\mu)=t(t-\mu)(e+\mu)^2/((t+\mu)(2t-\mu)^2)$ of (26) is differentiable at $\mu=0$ and
--   $$\left.\frac{d\pi^M}{d\mu}\right|_{\mu=0}>0.$$
--
--   Network effects therefore raise the symmetric profit when they are weak.
--
--   **Formalization Note** The page states this under $2t-e>0$. The statement adds $e>0$: at $e=0$ the factor $e+\mu$ of the derivative vanishes at $\mu=0$, so the derivative there is $0$ and the strict inequality fails. The derivative is two-sided (`HasDerivAt`); $\pi^M$ is smooth near $\mu=0$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, display dπᴹ/dμ|_{μ=0} > 0

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF p. 28: dπᴹ/dμ at μ = 0 is positive (for e > 0). -/
theorem deriv_profit_pos_at_zero (t e : ℝ) (ht : 0 < t) (he0 : 0 < e) (he : e < 2 * t) :
    ∃ d : ℝ, HasDerivAt (fun μ => piM t μ e) d 0 ∧ 0 < d := by sorry

end Multihoming.Hump
