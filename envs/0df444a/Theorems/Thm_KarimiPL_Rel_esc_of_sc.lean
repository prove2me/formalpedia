-- Prove2me | Theorems.Thm_KarimiPL_Rel_esc_of_sc
-- name    : KarimiPL.Rel.esc_of_sc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:05.229567+00:00
-- url     : https://prove2.me/theorems/0eee253b-e79a-43b9-85b1-0fc1f7211525
-- title:
--   Appendix A, p. 12 — SC with constant μ implies ESC with constant μ
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, let $\mathcal X^*$ be its set of global minimizers and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$. Let $\mu>0$. If $f$ is $\mu$-strongly convex,
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac\mu2\|y-x\|^2\quad\text{for all }x,y,$$
--   then $f$ is essentially strongly convex with the same constant: the inequality holds in particular for all $x,y$ with $x_p=y_p$.
--
--   This is the first link of the chain of Theorem 2.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "SC → ESC", p. 12

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem esc_of_sc {d : ℕ} (f : E d → ℝ) (p : E d → E d) (hp : IsProjSel f p)
    (μ : ℝ) (hμ : 0 < μ) (hSC : SC f μ) :
    ESC f p μ := by sorry

end KarimiPL.Rel
