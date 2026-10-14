-- Prove2me | Theorems.Thm_Multihoming_Hump_deriv_price_signs
-- name    : Multihoming.Hump.deriv_price_signs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:40.154268+00:00
-- url     : https://prove2.me/theorems/214b22fe-577e-419a-82a8-6355535b18b3
-- title:
--   Appendix A1, PDF p. 29 (printed p. 23) — dpᴹ/dμ > 0 at μ = 0 and dpᴹ/dμ < 0 at μ = t
-- statement:
--   Let $t>0$ and $0\le e<2t$. The symmetric price $p^M(\mu)=(t-\mu)(\mu+e)/(2t-\mu)$ of (26) is differentiable at $\mu=0$ and at $\mu=t$, with
--   $$\left.\frac{dp^M}{d\mu}\right|_{\mu=0}>0\qquad\text{and}\qquad\left.\frac{dp^M}{d\mu}\right|_{\mu=t}<0.$$
--
--   Weak network effects raise the price, and strong ones lower it.
--
--   **Formalization Note** "In case of partial multihoming" is pinned as $0\le e<2t$, the condition the appendix uses. Derivatives are two-sided (`HasDerivAt`); $p^M$ is smooth near $0$ and $t$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 29 (printed p. 23), Appendix A1, display dpᴹ/dμ|_{μ=0} > 0 and dpᴹ/dμ|_{μ=t} < 0

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF p. 29: dpᴹ/dμ is positive at μ = 0 and negative at μ = t. -/
theorem deriv_price_signs (t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    (∃ d : ℝ, HasDerivAt (fun μ => Multihoming.Thresholds.pM t μ e) d 0 ∧ 0 < d) ∧
    (∃ d : ℝ, HasDerivAt (fun μ => Multihoming.Thresholds.pM t μ e) d t ∧ d < 0) := by sorry

end Multihoming.Hump
