-- Prove2me | Theorems.Thm_LeveragedPayouts_Unregulated_eq33_35
-- name    : LeveragedPayouts.Unregulated.eq33_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:13.211705+00:00
-- url     : https://prove2.me/theorems/c16615ad-3cc3-4366-9845-40f3ba7e7775
-- title:
--   (33)–(35), p. 29 — the unregulated date-0 entrepreneur chooses x₀ = R/(2R − r₀) < 1, e₀ = πx₀ < π and πRf′(l₀)/(2(2R − r₀)) = r₀w*
-- statement:
--   Consider an economy with discount rate $R$, effort parameter $\pi$, technology $f$ and steady-state wage $w^*$, and a date-0 rate $0<r_0<R$. A date-0 entrepreneur solves program (31)–(32): choose a retained stake $x\in[0,1]$, labour $l>0$ and an incentive-compatible effort $e$ to maximize
--   $$\frac{W+(1-x)ef(l)}{r_0}-w^*l+\Big(xe-\frac{e^2}{2\pi}\Big)\frac{f(l)}{R}.$$
--   The program has a solution, and every solution $(e,l,x)$ satisfies
--   $$x=\frac{R}{2R-r_0}<1,\qquad e=\pi x=\frac{\pi R}{2R-r_0}<\pi,\qquad \frac{\pi R f'(l)}{2(2R-r_0)}=r_0w^* .$$
--
--   These are (33)–(35): with the rate cut below $R$, the entrepreneur pays out part of its future output, keeps less skin in the game and exerts less than the first-best effort.
--
--   **Formalization Note** The page prints (34) as $\pi R/(2R-r)$; the intended $r_0$ is used. $W$ is an arbitrary real number.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 29, §3.4.3, (31)–(35)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Firm

namespace LeveragedPayouts.Unregulated
theorem eq33_35 (E : Economy) (W r₀ : ℝ) (hr0 : 0 < r₀) (hr0R : r₀ < E.R) :
    (∃ e l x, IsMax31 E W r₀ e l x) ∧
    ∀ e l x, IsMax31 E W r₀ e l x →
      x = E.R / (2 * E.R - r₀) ∧ x < 1 ∧
      e = E.π * x ∧ e = E.π * E.R / (2 * E.R - r₀) ∧ e < E.π ∧
      E.π * E.R * deriv E.f l / (2 * (2 * E.R - r₀)) = r₀ * E.wstar := by sorry
end LeveragedPayouts.Unregulated
