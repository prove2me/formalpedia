-- Prove2me | Theorems.Thm_OkunsLaw_gapLaw_iff_ratio
-- name    : OkunsLaw.gapLaw_iff_ratio
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:20.76435+00:00
-- url     : https://prove2.me/theorems/e2ecdcbf-deb6-47f8-9a0d-cbefaab5ffcb
-- title:
--   Okun's gap law as $Y/\overline Y - 1 = c(\overline u - u)$
-- statement:
--   Let $Y_t$ be actual output, $\overline Y_t$ potential GDP, $u_t$ the actual unemployment rate and $\overline u_t$ the natural rate of unemployment in year $t$, and let $c\in\mathbb R$. If $\overline Y_t>0$, then the gap version of Okun's law
--   $$\frac{\overline Y_t - Y_t}{\overline Y_t} = c\,(u_t-\overline u_t)$$
--   holds if and only if
--   $$\frac{Y_t}{\overline Y_t} - 1 = c\,(\overline u_t - u_t).$$
--
--   This is the first rewriting in the derivation of the growth-rate form of Okun's law.
-- source:
--   Wikipedia, "Okun's law", revision oldid=1341356066 (https://en.wikipedia.org/w/index.php?title=Okun%27s_law&oldid=1341356066), section "Derivation of the growth rate form", first display (lines 1-2).

import Mathlib
import Definitions.Def_OkunsLaw_defs

namespace OkunsLaw

theorem gapLaw_iff_ratio (c : ℝ) (Y Ybar u ubar : ℕ → ℝ) (t : ℕ) (hYbar : 0 < Ybar t) :
    GapLaw c Y Ybar u ubar t ↔ Y t / Ybar t - 1 = c * (ubar t - u t) := by
  sorry

end OkunsLaw
