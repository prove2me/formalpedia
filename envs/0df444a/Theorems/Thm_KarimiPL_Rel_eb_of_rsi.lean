-- Prove2me | Theorems.Thm_KarimiPL_Rel_eb_of_rsi
-- name    : KarimiPL.Rel.eb_of_rsi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:58.026626+00:00
-- url     : https://prove2.me/theorems/990f89d7-4f9b-4be3-9f64-55417df40372
-- title:
--   Appendix A, p. 12 — RSI with constant μ implies EB with constant μ
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, let $\mathcal X^*$ be its set of global minimizers and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$. Let $\mu>0$. If $f$ satisfies the restricted secant inequality with constant $\mu$, $\langle\nabla f(x),x-x_p\rangle\ge\mu\|x_p-x\|^2$ for all $x$, then $f$ satisfies the error bound with the same constant: for every $x$,
--   $$\|\nabla f(x)\|\ge\mu\|x_p-x\|.$$
--
--   This is the fourth link of the chain of Theorem 2.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "RSI → EB", p. 12

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem eb_of_rsi {d : ℕ} (f : E d → ℝ) (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hRSI : RSI f p μ) :
    EB f p μ := by sorry

end KarimiPL.Rel
