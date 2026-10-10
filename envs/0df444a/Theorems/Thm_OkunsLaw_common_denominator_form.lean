-- Prove2me | Theorems.Thm_OkunsLaw_common_denominator_form
-- name    : OkunsLaw.common_denominator_form
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:48.728472+00:00
-- url     : https://prove2.me/theorems/7f9930cd-f080-4253-975e-eef5b988d194
-- title:
--   Okun's law: common-denominator form
-- statement:
--   Let $Y$, $\overline Y$, $u$, $\overline u$ be the series of actual output, potential GDP, actual unemployment rate and natural rate of unemployment, let $c\in\mathbb R$, and let $t$ be a year with $\overline Y_t>0$ and $\overline Y_{t+1}>0$. If the gap version of Okun's law holds with coefficient $c$ in both years $t$ and $t+1$, then, writing $\Delta x_t = x_{t+1}-x_t$,
--   $$\frac{\overline Y_t\,\Delta Y_t - Y_t\,\Delta\overline Y_t}{\overline Y_t\,(\overline Y_t+\Delta\overline Y_t)} = c\,(\Delta\overline u_t-\Delta u_t).$$
--
--   This is the step "putting both numerators over a common denominator" in the derivation of the growth-rate form.
-- source:
--   Wikipedia, "Okun's law", revision oldid=1341356066 (https://en.wikipedia.org/w/index.php?title=Okun%27s_law&oldid=1341356066), section "Derivation of the growth rate form", third display ("Putting both numerators over a common denominator").

import Mathlib
import Definitions.Def_OkunsLaw_defs

namespace OkunsLaw

theorem common_denominator_form (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
    (hYbar₀ : 0 < Ybar t) (hYbar₁ : 0 < Ybar (t + 1))
    (h₀ : GapLaw c Y Ybar u ubar t) (h₁ : GapLaw c Y Ybar u ubar (t + 1)) :
    (Ybar t * delta Y t - Y t * delta Ybar t) / (Ybar t * (Ybar t + delta Ybar t))
      = c * (delta ubar t - delta u t) := by
  sorry

end OkunsLaw
