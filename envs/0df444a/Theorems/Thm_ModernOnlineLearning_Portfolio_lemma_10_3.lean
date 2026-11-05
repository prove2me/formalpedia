-- Prove2me | Theorems.Thm_ModernOnlineLearning_Portfolio_lemma_10_3
-- name    : ModernOnlineLearning.Portfolio.lemma_10_3
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T13:53:22.537119+00:00
-- url     : https://prove2.me/theorems/855978b3-63ba-49b7-88af-002c230a578b
-- title:
--   Lemma 10.3, p. 173 — the empirical type maximizes the product of probabilities
-- statement:
--   Let $T\ge 1$ be an integer, let $x\in\mathbb{R}^d_{\ge 0}$ satisfy $\sum_{i=1}^d x_i = T$, and let $u\in\Delta^{d-1}$ be a point of the probability simplex. Then
--
--   $$\prod_{i=1}^d u_i^{x_i} \le \prod_{i=1}^d \left(\frac{x_i}{T}\right)^{x_i},$$
--
--   with the convention $0^0 := 1$.
--
--   **Formalization note.** Powers are real powers (`Real.rpow`), which satisfy $0^0=1$ and $0^a=0$ for $a>0$, matching the book's convention.
-- source:
--   Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, Section 10.3.1, Lemma 10.3, p. 173

import Mathlib
set_option autoImplicit false

namespace ModernOnlineLearning.Portfolio

/-- Lemma 10.3, p. 173. Real powers use `Real.rpow`, for which `0 ^ 0 = 1`. -/
theorem lemma_10_3 {d T : ℕ} (hT : 1 ≤ T) (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsum : ∑ i, x i = (T : ℝ)) (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    ∏ i, u i ^ x i ≤ ∏ i, (x i / (T : ℝ)) ^ x i := by sorry

end ModernOnlineLearning.Portfolio
