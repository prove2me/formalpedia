-- Prove2me | Theorems.Thm_Multihoming_Hump_deriv_profit_neg_at_t
-- name    : Multihoming.Hump.deriv_profit_neg_at_t
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:35.483787+00:00
-- url     : https://prove2.me/theorems/3db77905-1f8f-49dc-96ce-29899f4778e6
-- title:
--   Appendix A1, PDF p. 28 (printed p. 22) — dπᴹ/dμ at μ = t is negative
-- statement:
--   Let $t>0$ and $0\le e<2t$. The symmetric profit $\pi^M(\mu)=t(t-\mu)(e+\mu)^2/((t+\mu)(2t-\mu)^2)$ of (26) is differentiable at $\mu=t$ and
--   $$\left.\frac{d\pi^M}{d\mu}\right|_{\mu=t}<0.$$
--
--   Strong network effects therefore lower the symmetric profit.
--
--   **Formalization Note** The point $\mu=t$ is the boundary of Assumption 1(i) ($\mu<t$); the paper evaluates the closed form (26) there, and so does this statement. The derivative is two-sided (`HasDerivAt`); (26) is smooth near $\mu=t$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, display dπᴹ/dμ|_{μ=t} < 0

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF p. 28: dπᴹ/dμ at μ = t is negative. -/
theorem deriv_profit_neg_at_t (t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    ∃ d : ℝ, HasDerivAt (fun μ => piM t μ e) d t ∧ d < 0 := by sorry

end Multihoming.Hump
