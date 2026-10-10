-- Prove2me | Theorems.Thm_OkunsLaw_exact_growth_identity
-- name    : OkunsLaw.exact_growth_identity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:14.605775+00:00
-- url     : https://prove2.me/theorems/39caf705-641d-4341-ac13-856ca05b20ca
-- title:
--   Okun's law: exact growth-rate identity
-- statement:
--   Let $Y$, $\overline Y$, $u$, $\overline u$ be the series of actual output, potential GDP, actual unemployment rate and natural rate of unemployment, let $c\in\mathbb R$, and let $t$ be a year with $Y_t>0$, $\overline Y_t>0$ and $\overline Y_{t+1}>0$. If the gap version of Okun's law holds with coefficient $c$ in both years $t$ and $t+1$, then, writing $\Delta x_t = x_{t+1}-x_t$,
--   $$\frac{\Delta Y_t}{Y_t} - \frac{\Delta\overline Y_t}{\overline Y_t} = c\,(\Delta\overline u_t-\Delta u_t)\cdot\frac{\overline Y_t+\Delta\overline Y_t}{Y_t}.$$
--
--   This is the exact form of the step "multiplying the left hand side by $(\overline Y+\Delta\overline Y)/Y$, which is approximately equal to 1": the source then drops the factor $(\overline Y_t+\Delta\overline Y_t)/Y_t$, obtaining $\frac{\Delta Y}{Y} \approx \frac{\Delta\overline Y}{\overline Y} + c(\Delta\overline u-\Delta u)$.
-- source:
--   Wikipedia, "Okun's law", revision oldid=1341356066 (https://en.wikipedia.org/w/index.php?title=Okun%27s_law&oldid=1341356066), section "Derivation of the growth rate form", fourth and fifth displays ("Multiplying the left hand side by (Ybar+ΔYbar)/Y").

import Mathlib
import Definitions.Def_OkunsLaw_defs

namespace OkunsLaw

theorem exact_growth_identity (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
    (hY : 0 < Y t) (hYbar₀ : 0 < Ybar t) (hYbar₁ : 0 < Ybar (t + 1))
    (h₀ : GapLaw c Y Ybar u ubar t) (h₁ : GapLaw c Y Ybar u ubar (t + 1)) :
    growthRate Y t - growthRate Ybar t
      = c * (delta ubar t - delta u t) * ((Ybar t + delta Ybar t) / Y t) := by
  sorry

end OkunsLaw
