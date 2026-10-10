-- Prove2me | Theorems.Thm_OkunsLaw_growth_rate_form
-- name    : OkunsLaw.growth_rate_form
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:42.17149+00:00
-- url     : https://prove2.me/theorems/271b150e-fe65-40a9-861f-b903774909ab
-- title:
--   Okun's law: growth-rate form $\Delta Y/Y = k - c\,\Delta u$ with exact remainder
-- statement:
--   Let $Y$, $\overline Y$, $u$, $\overline u$ be the series of actual output, potential GDP, actual unemployment rate and natural rate of unemployment, let $c,k\in\mathbb R$, and let $t$ be a year with $Y_t>0$, $\overline Y_t>0$ and $\overline Y_{t+1}>0$. Write $\Delta x_t = x_{t+1}-x_t$. Assume
--
--   1. the gap version of Okun's law $\dfrac{\overline Y_s - Y_s}{\overline Y_s} = c\,(u_s-\overline u_s)$ holds for $s=t$ and $s=t+1$;
--   2. the natural rate of unemployment does not change: $\Delta\overline u_t = 0$;
--   3. full-employment output grows at rate $k$: $\Delta\overline Y_t/\overline Y_t = k$.
--
--   Then
--   $$\frac{\Delta Y_t}{Y_t} = k - c\,\Delta u_t - c\,\Delta u_t\left(\frac{\overline Y_t+\Delta\overline Y_t}{Y_t}-1\right).$$
--
--   This is the growth-rate (difference) form of Okun's law, $\frac{\Delta Y}{Y}\approx k - c\,\Delta u$, with the approximation made exact: the last term is exactly the error committed by replacing the factor $(\overline Y_t+\Delta\overline Y_t)/Y_t$ with $1$.
--
--   **Formalization Note** The source's approximations $\Delta\overline u\approx 0$ and $\Delta\overline Y/\overline Y\approx k$ are taken as exact hypotheses 2 and 3; the approximation $(\overline Y+\Delta\overline Y)/Y\approx 1$ is replaced by the explicit remainder term.
-- source:
--   Wikipedia, "Okun's law", revision oldid=1341356066 (https://en.wikipedia.org/w/index.php?title=Okun%27s_law&oldid=1341356066), section "Mathematical statements" (difference version ΔY/Y = k − cΔu) and section "Derivation of the growth rate form", final display.

import Mathlib
import Definitions.Def_OkunsLaw_defs

namespace OkunsLaw

theorem growth_rate_form (c k : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
    (hY : 0 < Y t) (hYbar₀ : 0 < Ybar t) (hYbar₁ : 0 < Ybar (t + 1))
    (h₀ : GapLaw c Y Ybar u ubar t) (h₁ : GapLaw c Y Ybar u ubar (t + 1))
    (hnatural : delta ubar t = 0) (hpotential : growthRate Ybar t = k) :
    growthRate Y t
      = k - c * delta u t - c * delta u t * ((Ybar t + delta Ybar t) / Y t - 1) := by
  sorry

end OkunsLaw
