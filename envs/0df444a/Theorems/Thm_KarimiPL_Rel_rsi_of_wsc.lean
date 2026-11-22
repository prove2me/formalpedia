-- Prove2me | Theorems.Thm_KarimiPL_Rel_rsi_of_wsc
-- name    : KarimiPL.Rel.rsi_of_wsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:57.932989+00:00
-- url     : https://prove2.me/theorems/f39c5e6c-6bf8-44e4-b760-6e5db5f5d0cf
-- title:
--   Appendix A, p. 12 — WSC with constant μ implies RSI with constant μ/2
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, let $\mathcal X^*$ be its set of global minimizers and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$. Let $\mu>0$. If $f$ satisfies weak strong convexity with constant $\mu$, then $f$ satisfies the restricted secant inequality with constant $\mu/2$: for every $x$,
--   $$\langle\nabla f(x),x-x_p\rangle\ge\frac\mu2\|x_p-x\|^2.$$
--
--   This is the third link of the chain of Theorem 2.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "WSC → RSI", p. 12

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem rsi_of_wsc {d : ℕ} (f : E d → ℝ) (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hWSC : WSC f p μ) :
    RSI f p (μ / 2) := by sorry

end KarimiPL.Rel
