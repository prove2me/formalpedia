-- Prove2me | Theorems.Thm_OkunsLaw_ratio_annual_difference
-- name    : OkunsLaw.ratio_annual_difference
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:48.535622+00:00
-- url     : https://prove2.me/theorems/98ff96e3-2c97-4d27-a358-1f5b3a1fbe26
-- title:
--   Okun's law: annual difference of $Y/\overline Y$
-- statement:
--   Let $Y$, $\overline Y$, $u$, $\overline u$ be the series of actual output, potential GDP, actual unemployment rate and natural rate of unemployment, let $c\in\mathbb R$, and let $t$ be a year with $\overline Y_t>0$ and $\overline Y_{t+1}>0$. Suppose the gap version of Okun's law
--   $$\frac{\overline Y_s - Y_s}{\overline Y_s} = c\,(u_s-\overline u_s)$$
--   holds for both $s=t$ and $s=t+1$ (with the same $c$). Then, writing $\Delta x_t = x_{t+1}-x_t$,
--   $$\Delta\!\left(\frac{Y}{\overline Y}\right)_t = \frac{Y_t+\Delta Y_t}{\overline Y_t+\Delta\overline Y_t} - \frac{Y_t}{\overline Y_t} = c\,(\Delta\overline u_t - \Delta u_t).$$
--
--   This is the step "taking annual differences on both sides" in the derivation of the growth-rate form.
-- source:
--   Wikipedia, "Okun's law", revision oldid=1341356066 (https://en.wikipedia.org/w/index.php?title=Okun%27s_law&oldid=1341356066), section "Derivation of the growth rate form", second display ("Taking annual differences on both sides").

import Mathlib
import Definitions.Def_OkunsLaw_defs

namespace OkunsLaw

theorem ratio_annual_difference (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ)
    (hYbar₀ : 0 < Ybar t) (hYbar₁ : 0 < Ybar (t + 1))
    (h₀ : GapLaw c Y Ybar u ubar t) (h₁ : GapLaw c Y Ybar u ubar (t + 1)) :
    delta (fun s => Y s / Ybar s) t
        = (Y t + delta Y t) / (Ybar t + delta Ybar t) - Y t / Ybar t ∧
      delta (fun s => Y s / Ybar s) t = c * (delta ubar t - delta u t) := by
  sorry

end OkunsLaw
