-- Prove2me | Theorems.Thm_Orabona2019_theorem_2_13_faithful
-- name    : Orabona2019.theorem_2_13_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:30:46.529728+00:00
-- url     : https://prove2.me/theorems/8a7f78d5-1224-41ea-a562-212fbe906af1
-- title:
--   Theorem 2.13, with the constant-step bound for possibly unbounded V
-- statement:
--   Let $V$ be a non-empty closed convex subset of a real Hilbert space, $T\ge1$, and $\ell_1,\dots,\ell_T$ convex and differentiable on open sets containing $V$. Run projected Online Gradient Descent from $x_1\in V$: $g_t=\nabla\ell_t(x_t)$ and $x_{t+1}=\Pi_V(x_t-\eta_tg_t)$, with step sizes $0<\eta_{t+1}\le\eta_t$. Then for every $u\in V$:
--
--   1. if $V$ is bounded, with diameter $D$, $$\sum_{t=1}^T\big(\ell_t(x_t)-\ell_t(u)\big)\le\frac{D^2}{2\eta_T}+\sum_{t=1}^T\frac{\eta_t}2\|g_t\|^2-\frac{\|x_{T+1}-u\|^2}{2\eta_T};$$
--   2. if $\eta_t=\eta$ for all $t=1,\dots,T$ ($V$ possibly unbounded), $$\sum_{t=1}^T\big(\ell_t(x_t)-\ell_t(u)\big)\le\frac{\|u-x_1\|^2}{2\eta}+\frac\eta2\sum_{t=1}^T\|g_t\|^2-\frac{\|x_{T+1}-u\|^2}{2\eta}.$$
--
--   This is Theorem 2.13 of Orabona's book with both of its conclusions, the basic regret bound of projected Online Gradient Descent. The existing theorem ModernOnlineLearning.OGD.theorem_2_13 is part 1; part 2 does not follow from it, since $D\ge\|u-x_1\|$, and it also covers unbounded $V$.
--
--   **Formalization Note** Part 1 assumes boundedness because the diameter of an unbounded set is $0$ in Mathlib, whereas the book's bound is then vacuous ($D=\infty$). The projection is any metric projection onto $V$.
-- source:
--   Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 13, Theorem 2.13

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ModernOnlineLearning_OGD_Defs

open ModernOnlineLearning.OGD

theorem Orabona2019.theorem_2_13_faithful {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V)
    (loss : ℕ → E → ℝ) (η : ℕ → ℝ) (x g : ℕ → E) (T : ℕ)
    (hT : 1 ≤ T) (u : E) (hu : u ∈ V)
    (hloss : ∀ t ∈ Finset.Icc 1 T,
      ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ ConvexOn ℝ U (loss t) ∧ DifferentiableOn ℝ (loss t) U)
    (hη : ∀ t ∈ Finset.Icc 1 T, 0 < η t)
    (hmono : ∀ t ∈ Finset.Icc 1 (T - 1), η (t + 1) ≤ η t)
    (hrun : IsOGDRun V loss η x g T) :
    (Bornology.IsBounded V →
      regret loss x u T ≤
        Metric.diam V ^ 2 / (2 * η T) +
          ∑ t ∈ Finset.Icc 1 T, (η t / 2) * ‖g t‖ ^ 2 -
            ‖x (T + 1) - u‖ ^ 2 / (2 * η T)) ∧
    (∀ η₀ : ℝ, (∀ t ∈ Finset.Icc 1 T, η t = η₀) →
      regret loss x u T ≤
        ‖u - x 1‖ ^ 2 / (2 * η₀) + (η₀ / 2) * ∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2 -
          ‖x (T + 1) - u‖ ^ 2 / (2 * η₀)) := by sorry
