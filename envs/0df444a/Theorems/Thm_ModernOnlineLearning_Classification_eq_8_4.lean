-- Prove2me | Theorems.Thm_ModernOnlineLearning_Classification_eq_8_4
-- name    : ModernOnlineLearning.Classification.eq_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:40.432122+00:00
-- url     : https://prove2.me/theorems/7ed8b0de-0363-413d-809a-3d117033c051
-- title:
--   Eq. (8.4), p. 145 — Perceptron comparator inequality (corrected)
-- statement:
--   Let $\tau_t$ indicate the update rounds of Algorithm 8.2, let $M=\sum_{t=1}^T\tau_t$, and suppose $\|z_t\|_2\le R$. For every competitor $u\in\mathbb R^d$,
--
--   $$
--   \sum_{t=1}^T\tau_ty_t\langle z_t,u\rangle
--   \le\|u\|_2\sqrt{\sum_{t=1}^T\tau_t\|z_t\|_2^2}
--   \le\|u\|_2R\sqrt M.
--   $$
--
--   This is the comparator estimate used to obtain the mistake inequality (8.5).
--
--   **Formalization Note** The printed (8.4) adds $-\tau_ty_t\langle z_t,x_t\rangle$ on the left. That version is false for the actual Perceptron iterates: with $z_1=1,z_2=-1$, $y_1=y_2=1$, and $u=0$, its left side is $1$ and its right side $0$. The Lean statement drops that nonnegative summand, preserving the valid inequality needed for (8.5). The source text is retained verbatim in the milestone record.
-- source:
--   Orabona, arXiv:1912.13213v10, Eq. (8.4), proof of Theorem 8.2, p. 145 (corrected comparator form)

import Mathlib
import Definitions.Def_ModernOnlineLearning_Classification_Perceptron

namespace ModernOnlineLearning.Classification

/-- Orabona, Eq. (8.4), p. 145, with its invalid `-⟨τ_t y_t z_t,x_t⟩`
summand omitted from the left. The comparator term is the part used in Eq. (8.5). -/
theorem eq_8_4 {d : ℕ} (T : ℕ) (z : ℕ → ModernOnlineLearning.Adaptive.Vec d) (y : ℕ → ℝ)
    (hy : ∀ t ∈ Finset.Icc 1 T, y t = -1 ∨ y t = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ t ∈ Finset.Icc 1 T, ‖z t‖ ≤ R) (u : ModernOnlineLearning.Adaptive.Vec d) :
    (∑ t ∈ Finset.Icc 1 T, mistakeIndicator z y t * y t * inner ℝ (z t) u) ≤
        ‖u‖ * Real.sqrt (∑ t ∈ Finset.Icc 1 T,
          mistakeIndicator z y t * ‖z t‖ ^ 2) ∧
      ‖u‖ * Real.sqrt (∑ t ∈ Finset.Icc 1 T,
          mistakeIndicator z y t * ‖z t‖ ^ 2) ≤
        ‖u‖ * R * Real.sqrt (mistakes z y T) := by sorry

end ModernOnlineLearning.Classification
