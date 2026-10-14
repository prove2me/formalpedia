-- Prove2me | Theorems.Thm_Multihoming_Hump_deriv_profit_factor
-- name    : Multihoming.Hump.deriv_profit_factor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:34.216217+00:00
-- url     : https://prove2.me/theorems/9b5e4d82-ac1b-43cb-b9e2-02cf780007aa
-- title:
--   Appendix A1, PDF p. 28 (printed p. 22) — dπᴹ/dμ = 2t(e+μ)(e+t)/((t+μ)²(2t−μ)³)·(r₁ − μ)(r₂ + μ)
-- statement:
--   Let $t>0$, $0\le e<2t$ and $0\le\mu\le t$. The symmetric profit $\pi^M(\mu)=t(t-\mu)(e+\mu)^2/((t+\mu)(2t-\mu)^2)$ of (26), as a function of $\mu$, is differentiable at $\mu$ with
--   $$\frac{d\pi^M}{d\mu}=\frac{2t\,(e+\mu)(e+t)}{(t+\mu)^2(2t-\mu)^3}\,(r_1-\mu)(r_2+\mu),$$
--   where $r_1=\dfrac{t\sqrt{3(4t^2-e^2)}-2t^2+et}{2(e+t)}$ and $r_2=\dfrac{t\left(2t-e+\sqrt{3(4t^2-e^2)}\right)}{2(e+t)}$.
--
--   The factorization reduces the sign of $d\pi^M/d\mu$ on $[0,t]$ to the sign of $r_1-\mu$.
--
--   **Formalization Note** The derivative is the two-sided derivative (`HasDerivAt`); $\pi^M$ is smooth near every $\mu\in[0,t]$ since $t+\mu>0$ and $2t-\mu>0$ there. The hypotheses $0\le e<2t$ keep the square-root argument positive and $e+t>0$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, display dπᴹ/dμ and definitions of r₁, r₂

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF p. 28: dπᴹ/dμ = 2t(e + μ)(e + t)/((t + μ)²(2t − μ)³) · (r₁ − μ)(r₂ + μ). -/
theorem deriv_profit_factor (t e μ : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t)
    (hμ0 : 0 ≤ μ) (hμt : μ ≤ t) :
    HasDerivAt (fun x => piM t x e)
      (2 * t * (e + μ) * (e + t) / ((t + μ) ^ 2 * (2 * t - μ) ^ 3) *
        (r1 t e - μ) * (r2 t e + μ)) μ := by sorry

end Multihoming.Hump
