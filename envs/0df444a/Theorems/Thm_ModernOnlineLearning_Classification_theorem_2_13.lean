-- Prove2me | Theorems.Thm_ModernOnlineLearning_Classification_theorem_2_13
-- name    : ModernOnlineLearning.Classification.theorem_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:40.434992+00:00
-- url     : https://prove2.me/theorems/3175d5b2-1da0-43a9-913c-7aaa843d4fae
-- title:
--   Theorem 2.13, p. 13 — constant-step gradient bound for linear losses on all of Euclidean space
-- statement:
--   Consider linear losses with gradient vectors $g_t\in\mathbb R^d$. Let $\eta>0$ be fixed and let $x_{t+1}=x_t-\eta g_t$ for rounds $t=1,\ldots,T$. For every $u\in\mathbb R^d$,
--
--   $$
--   \sum_{t=1}^T\langle g_t,x_t-u\rangle
--   \le \frac{\|u-x_1\|_2^2}{2\eta}
--      +\frac\eta2\sum_{t=1}^T\|g_t\|_2^2
--      -\frac{\|x_{T+1}-u\|_2^2}{2\eta}.
--   $$
--
--   This is the constant-step part of Theorem 2.13 specialized to the unprojected linear losses used in the Perceptron analysis.
--
--   **Formalization Note** The book states the theorem for a closed convex feasible set and convex differentiable losses. The Lean statement uses the stated linear-loss, whole-space specialization, so the linear loss difference is exactly $\langle g_t,x_t-u\rangle$. No bounded diameter is needed in this part.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 2.13, constant-step clause, p. 13; specialization used in proof of Theorem 8.2, p. 145

import Mathlib
import Definitions.Def_ModernOnlineLearning_Classification_Perceptron

namespace ModernOnlineLearning.Classification

/-- Orabona, Theorem 2.13, constant-step linear-loss case on all of `ℝ^d`, p. 13.
The update is unprojected gradient descent. -/
theorem theorem_2_13 {d : ℕ} (T : ℕ) (η : ℝ) (hη : 0 < η)
    (g x : ℕ → ModernOnlineLearning.Adaptive.Vec d)
    (hrun : ∀ t ∈ Finset.Icc 1 T, x (t + 1) = x t - η • g t)
    (u : ModernOnlineLearning.Adaptive.Vec d) :
    (∑ t ∈ Finset.Icc 1 T, inner ℝ (g t) (x t - u)) ≤
      ‖u - x 1‖ ^ 2 / (2 * η) +
        η / 2 * (∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2) -
        ‖x (T + 1) - u‖ ^ 2 / (2 * η) := by sorry

end ModernOnlineLearning.Classification
