-- Prove2me | Theorems.Thm_FracRiccati_Radius_kershaw_A_41
-- name    : FracRiccati.Radius.kershaw_A_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:21.553915+00:00
-- url     : https://prove2.me/theorems/6fe79e06-06cb-4a0c-9512-bda7fc2a683f
-- title:
--   (A.41), p. 27 — Kershaw's inequalities for the Gamma ratio Γ(x+1)/Γ(x+s)
-- statement:
--   **Kershaw's inequalities.** For every $x>0$ and every $s\in(0,1)$,
--   $$\Big(x+\frac s2\Big)^{1-s}<\frac{\Gamma(x+1)}{\Gamma(x+s)}<\Big(x-\frac12+\sqrt{s+\frac14}\Big)^{1-s}. \qquad (A.41)$$
--
--   These two-sided bounds on "ratios of close terms" of the Gamma function (Kershaw, 1983) control the factor $\Gamma(\alpha k+1)/\Gamma(\alpha k+\alpha+1)$ of the recursion (3.19); Appendix B uses the left inequality, in the reciprocal form $\Gamma(x+s)/\Gamma(x+1)<(x+s/2)^{s-1}$ (B.45), with $(x,s)=(\alpha(k+1),1-\alpha)$, $(2\alpha k,\alpha)$, $(\alpha(k+1)-1,2-\alpha)$ and $(2\alpha k,\alpha-1)$.
--
--   **Formalization Note** Both inequalities are stated, with the paper's range $x>0$, $s\in(0,1)$ open at both ends (at $s=1$ the chain degenerates to equalities, and Appendix B treats the endpoint cases separately). The powers are real powers of positive bases ($x-\tfrac12+\sqrt{s+\tfrac14}>x>0$).
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 27, §A.2, (A.41) (Kershaw 1983)

import Mathlib

namespace FracRiccati.Radius

theorem kershaw_A_41 (x s : ℝ) (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    (x + s / 2) ^ (1 - s) < Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
    Real.Gamma (x + 1) / Real.Gamma (x + s) < (x - 1 / 2 + Real.sqrt (s + 1 / 4)) ^ (1 - s) := by sorry

end FracRiccati.Radius
