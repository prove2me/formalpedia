-- Prove2me | Theorems.Thm_ModernOnlineLearning_Classification_eq_8_5
-- name    : ModernOnlineLearning.Classification.eq_8_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:54.525012+00:00
-- url     : https://prove2.me/theorems/bafae09a-1371-4fcc-a3c6-b6801482c59f
-- title:
--   Eq. (8.5), p. 145 — mistakes bounded by margin and hinge loss
-- statement:
--   For Algorithm 8.2 with $\|z_t\|_2\le R$, let $M=\sum_{t=1}^T\tau_t$ and let $\ell_1$ be the hinge loss. Every $u\in\mathbb R^d$ satisfies
--
--   $$
--   M\le R\|u\|_2\sqrt M
--      +\sum_{t=1}^T\tau_t\ell_1(\langle z_t,u\rangle,y_t)
--   \le R\|u\|_2\sqrt M+L_1(u).
--   $$
--
--   This is the implicit mistake inequality to which Lemma 4.29 applies at $q=1$.
--
--   **Formalization Note** Labels are restricted to $\{-1,1\}$ on rounds $1,\ldots,T$ and $R\ge0$ is explicit. A zero score is an update and a mistake.
-- source:
--   Orabona, arXiv:1912.13213v10, Eq. (8.5), proof of Theorem 8.2, p. 145

import Mathlib
import Definitions.Def_ModernOnlineLearning_Classification_Perceptron

namespace ModernOnlineLearning.Classification

/-- Orabona, Eq. (8.5), p. 145, including its bound by the full hinge loss. -/
theorem eq_8_5 {d : ℕ} (T : ℕ) (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (hy : ∀ t ∈ Finset.Icc 1 T, y t = -1 ∨ y t = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ t ∈ Finset.Icc 1 T, ‖z t‖ ≤ R) (u : ModernOnlineLearning.Adaptive.Vec d) :
    mistakes z y T ≤
        ‖u‖ * R * Real.sqrt (mistakes z y T) +
          (∑ t ∈ Finset.Icc 1 T,
            mistakeIndicator z y t * hingePower 1 (inner ℝ (z t) u) (y t)) ∧
      ‖u‖ * R * Real.sqrt (mistakes z y T) +
          (∑ t ∈ Finset.Icc 1 T,
            mistakeIndicator z y t * hingePower 1 (inner ℝ (z t) u) (y t)) ≤
        ‖u‖ * R * Real.sqrt (mistakes z y T) + cumulativeHinge z y T u 1 := by sorry

end ModernOnlineLearning.Classification
