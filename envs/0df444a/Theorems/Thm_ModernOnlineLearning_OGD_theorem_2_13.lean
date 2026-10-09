-- Prove2me | Theorems.Thm_ModernOnlineLearning_OGD_theorem_2_13
-- name    : ModernOnlineLearning.OGD.theorem_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:51.186131+00:00
-- url     : https://prove2.me/theorems/29fbf0eb-0839-40a2-9e14-af0dd289d810
-- title:
--   Theorem 2.13 — projected OGD regret with nonincreasing steps
-- statement:
--   Let $V$ be a nonempty closed convex set of finite diameter $D=\sup_{x,y\in V}\|x-y\|$. For $T\ge1$, let $\ell_1,\ldots,\ell_T$ be convex and differentiable on open sets containing $V$, and let $(x_t,g_t)$ follow Algorithm 2.1 with positive nonincreasing step sizes $\eta_t$. Then every $u\in V$ satisfies
--   $$\operatorname{Regret}_T(u)\le\frac{D^2}{2\eta_T}+\sum_{t=1}^T\frac{\eta_t}{2}\|g_t\|^2-\frac{\|x_{T+1}-u\|^2}{2\eta_T}.$$
--
--   This gives a time-varying-step regret guarantee while retaining the terminal correction term. The constant-step clause of the same theorem is a companion item.
--
--   **Formalization Note** $D$ is `Metric.diam V`; boundedness ensures this is the actual finite diameter. The horizon is positive because the formula divides by $\eta_T$. The ambient space is a complete real inner-product space.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 2.13, p. 13, first displayed bound

import Mathlib
import Definitions.Def_ModernOnlineLearning_OGD_Defs

namespace ModernOnlineLearning.OGD

/-- Orabona, Theorem 2.13, p. 13: the variable-step regret bound, including the
terminal negative squared-distance term. -/
theorem theorem_2_13 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V) (hb : Bornology.IsBounded V)
    (loss : ℕ → E → ℝ) (η : ℕ → ℝ) (x g : ℕ → E) (T : ℕ)
    (hT : 1 ≤ T) (u : E) (hu : u ∈ V)
    (hloss : ∀ t ∈ Finset.Icc 1 T,
      ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ ConvexOn ℝ U (loss t) ∧ DifferentiableOn ℝ (loss t) U)
    (hη : ∀ t ∈ Finset.Icc 1 T, 0 < η t)
    (hmono : ∀ t ∈ Finset.Icc 1 (T - 1), η (t + 1) ≤ η t)
    (hrun : IsOGDRun V loss η x g T) :
    regret loss x u T ≤
      Metric.diam V ^ 2 / (2 * η T) +
        ∑ t ∈ Finset.Icc 1 T, (η t / 2) * ‖g t‖ ^ 2 -
          ‖x (T + 1) - u‖ ^ 2 / (2 * η T) := by sorry

end ModernOnlineLearning.OGD
