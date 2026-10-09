-- Prove2me | Theorems.Thm_ModernOnlineLearning_OGD_lemma_2_12
-- name    : ModernOnlineLearning.OGD.lemma_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:48.749984+00:00
-- url     : https://prove2.me/theorems/a107a098-23c8-4214-a7b1-bfa9bb27ba5f
-- title:
--   Lemma 2.12 — one projected gradient step
-- statement:
--   Let $V$ be nonempty, closed, and convex; let $\ell_t$ be convex and differentiable on an open set containing $V$; let $x_t,u\in V$, $\eta_t>0$, $g_t=\nabla\ell_t(x_t)$, and $x_{t+1}=\Pi_V(x_t-\eta_tg_t)$. Then
--   $$\eta_t(\ell_t(x_t)-\ell_t(u))\le\eta_t\langle g_t,x_t-u\rangle\le\frac12\|x_t-u\|^2-\frac12\|x_{t+1}-u\|^2+\frac{\eta_t^2}{2}\|g_t\|^2.$$
--
--   This is the per-round estimate summed in the regret theorem.
--
--   **Formalization Note** Membership of $x_t$ in $V$ is explicit, as required by Algorithm 2.1. The ambient space is a complete real inner-product space.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 2.12, p. 13

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

namespace ModernOnlineLearning.OGD

/-- Orabona, Lemma 2.12, p. 13: the two one-step inequalities for projected
online gradient descent. -/
theorem lemma_2_12 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V) (loss : E → ℝ) (x xn g u : E) (η : ℝ)
    (hx : x ∈ V) (hu : u ∈ V) (hη : 0 < η)
    (hopen : ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ ConvexOn ℝ U loss ∧ DifferentiableOn ℝ loss U)
    (hg : HasGradientAt loss g x)
    (hxn : OnlineConvexOpt.FirstOrder.IsMetricProjection V (x - η • g) xn) :
    η * (loss x - loss u) ≤ η * inner ℝ g (x - u) ∧
      η * inner ℝ g (x - u) ≤
        (1 / 2 : ℝ) * ‖x - u‖ ^ 2 - (1 / 2 : ℝ) * ‖xn - u‖ ^ 2 +
          (η ^ 2 / 2) * ‖g‖ ^ 2 := by sorry

end ModernOnlineLearning.OGD
