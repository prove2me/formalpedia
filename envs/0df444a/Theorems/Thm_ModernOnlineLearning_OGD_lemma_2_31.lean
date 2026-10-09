-- Prove2me | Theorems.Thm_ModernOnlineLearning_OGD_lemma_2_31
-- name    : ModernOnlineLearning.OGD.lemma_2_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:20.508514+00:00
-- url     : https://prove2.me/theorems/c018e517-ddb9-49f5-bd59-33c515dfd187
-- title:
--   Lemma 2.31 — one projected subgradient step
-- statement:
--   Let $V$ be nonempty, closed, and convex; let $x_t,u\in V$ and $\eta_t>0$. If $g_t$ is a subgradient of $\ell_t$ at $x_t$ and $x_{t+1}=\Pi_V(x_t-\eta_tg_t)$, then
--   $$\eta_t(\ell_t(x_t)-\ell_t(u))\le\eta_t\langle g_t,x_t-u\rangle\le\frac12\|x_t-u\|^2-\frac12\|x_{t+1}-u\|^2+\frac{\eta_t^2}{2}\|g_t\|^2.$$
--
--   This extends the per-round OGD estimate to subgradient choices.
--
--   **Formalization Note** Losses are real valued on $V$, and the subgradient inequality is required only against points of $V$. A full-space subgradient as in Definition 2.20 implies this relative condition.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 2.31, p. 19

import Mathlib
import Definitions.Def_ModernOnlineLearning_OGD_Defs

namespace ModernOnlineLearning.OGD

/-- Orabona, Lemma 2.31, p. 19: the projected subgradient step obeys the
same one-step regret inequalities. -/
theorem lemma_2_31 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V) (loss : E → ℝ) (x xn g u : E) (η : ℝ)
    (hx : x ∈ V) (hu : u ∈ V) (hη : 0 < η)
    (hg : IsSubgradientOn V loss x g)
    (hxn : OnlineConvexOpt.FirstOrder.IsMetricProjection V (x - η • g) xn) :
    η * (loss x - loss u) ≤ η * inner ℝ g (x - u) ∧
      η * inner ℝ g (x - u) ≤
        (1 / 2 : ℝ) * ‖x - u‖ ^ 2 - (1 / 2 : ℝ) * ‖xn - u‖ ^ 2 +
          (η ^ 2 / 2) * ‖g‖ ^ 2 := by sorry

end ModernOnlineLearning.OGD
