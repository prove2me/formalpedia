-- Prove2me | Theorems.Thm_KarimiPL_Rel_wsc_of_esc
-- name    : KarimiPL.Rel.wsc_of_esc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:59.034826+00:00
-- url     : https://prove2.me/theorems/ed0809c4-34a8-48b7-b7b4-74ad2cb19845
-- title:
--   Appendix A, p. 12 — ESC with constant μ implies WSC with constant μ
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, let $\mathcal X^*$ be its set of global minimizers and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$. Let $\mu>0$. If $f$ satisfies essential strong convexity with constant $\mu$ (the strong-convexity inequality for all $x,y$ with $x_p=y_p$), then $f$ satisfies weak strong convexity with constant $\mu$: for every $x$,
--   $$f^*\ge f(x)+\langle\nabla f(x),x_p-x\rangle+\frac\mu2\|x_p-x\|^2,$$
--   where $f^*=f(x_p)$ is the optimal value.
--
--   This is the second link of the chain of Theorem 2.
--
--   **Formalization Note** $f^*$ appears as $f(p(x))$, the value of $f$ at the projected point.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "ESC → WSC", p. 12

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem wsc_of_esc {d : ℕ} (f : E d → ℝ) (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hESC : ESC f p μ) :
    WSC f p μ := by sorry

end KarimiPL.Rel
