-- Prove2me | Theorems.Thm_ModernOnlineLearning_Classification_theorem_8_2
-- name    : ModernOnlineLearning.Classification.theorem_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:45.206374+00:00
-- url     : https://prove2.me/theorems/385270f7-e3d1-45b8-a496-8f4dbb3603e4
-- title:
--   Theorem 8.2, p. 144 — Perceptron mistake bound against every hinge power
-- statement:
--   Let $(z_t,y_t)_{t=1}^T$ be any sequence with $z_t\in\mathbb R^d$, $y_t\in\{-1,1\}$, and $\|z_t\|_2\le R$. Run Algorithm 8.2 and write $M$ for its number of mistakes, counting zero-score predictions as mistakes. For every $u\in\mathbb R^d$ and every real $q\ge1$, put $L_q(u)=\sum_{t=1}^T\max(1-y_t\langle z_t,u\rangle,0)^q$. Then
--
--   $$
--   M-L_q(u)\le \frac{q^2R^2\|u\|_2^2}{2}
--      +qR\|u\|_2\sqrt{\frac{q^2R^2\|u\|_2^2}{4}+L_q(u)}.
--   $$
--
--   The bound compares the Perceptron's mistakes simultaneously with the hinge-power loss of every fixed linear competitor.
--
--   **Formalization Note** Rounds are indexed from $1$. The auxiliary feature set $X\subseteq\mathbb R^d$ is omitted because the theorem quantifies over the sequence itself and uses only its norm bound. The implicit $R\ge0$ is explicit; $R=0$ and $T=0$ are included. The square-root argument is nonnegative since hinge-power losses are nonnegative for $q\ge1$.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 8.2, p. 144; Algorithm 8.2 and hinge-power loss, p. 143

import Mathlib
import Definitions.Def_ModernOnlineLearning_Classification_Perceptron

namespace ModernOnlineLearning.Classification

/-- Orabona, Theorem 8.2, p. 144: the Perceptron mistake bound for every
competitor and every real hinge power `q ≥ 1`. -/
theorem theorem_8_2 {d : ℕ} (T : ℕ) (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (hy : ∀ t ∈ Finset.Icc 1 T, y t = -1 ∨ y t = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ t ∈ Finset.Icc 1 T, ‖z t‖ ≤ R)
    (u : ModernOnlineLearning.Adaptive.Vec d) (q : ℝ) (hq : 1 ≤ q) :
    mistakes z y T - cumulativeHinge z y T u q ≤
      q ^ 2 * R ^ 2 * ‖u‖ ^ 2 / 2 +
        q * R * ‖u‖ * Real.sqrt
          (q ^ 2 * R ^ 2 * ‖u‖ ^ 2 / 4 + cumulativeHinge z y T u q) := by sorry

end ModernOnlineLearning.Classification
