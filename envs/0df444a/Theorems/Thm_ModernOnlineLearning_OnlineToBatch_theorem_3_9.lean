-- Prove2me | Theorems.Thm_ModernOnlineLearning_OnlineToBatch_theorem_3_9
-- name    : ModernOnlineLearning.OnlineToBatch.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:32.618047+00:00
-- url     : https://prove2.me/theorems/804e1c3e-3f74-419e-b377-7d4176154b3f
-- title:
--   Theorem 3.9 — Hoeffding–Azuma inequality for bounded martingale differences
-- statement:
--   Let $Z_0,\ldots,Z_T$ be an integrable martingale on a probability space, adapted to a filtration. Suppose $T\ge1$, $B>0$, $\varepsilon\ge0$, and $|Z_t-Z_{t-1}|\le B$ almost surely for every $1\le t\le T$. Then both tails satisfy
--
--   $$\mathbb P(Z_T-Z_0\ge\varepsilon),\ \mathbb P(Z_0-Z_T\ge\varepsilon)\ \le\ \exp\!\left(-\frac{\varepsilon^2}{2B^2T}\right).$$
--
--   This concentration bound supplies the two deviations used in the high-probability online-to-batch conversion.
--
--   **Formalization Note** The source leaves the threshold and denominator domain implicit. The conditions $\varepsilon\ge0$, $B>0$ and $T\ge1$ make its printed formula valid and defined. The martingale is indexed only through $T$, matching the finite sequence in the book.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 3.9, p. 27 (PDF p. 39)

import Mathlib

namespace ModernOnlineLearning.OnlineToBatch

/-- Orabona, arXiv:1912.13213v10, Theorem 3.9, p. 27. -/
theorem theorem_3_9 {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (T : ℕ) (ℱ : MeasureTheory.Filtration (Fin (T + 1)) ‹MeasurableSpace Ω›)
    (Z : Fin (T + 1) → Ω → ℝ) (B ε : ℝ)
    (hT : 1 ≤ T) (hB : 0 < B) (hε : 0 ≤ ε)
    (hZ : MeasureTheory.Martingale Z ℱ μ)
    (hZint : ∀ t : Fin (T + 1), MeasureTheory.Integrable (Z t) μ)
    (hdiff : ∀ t : Fin T,
      ∀ᵐ ω ∂μ, |Z ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩ ω -
        Z ⟨t.val, Nat.lt_trans t.isLt (Nat.lt_succ_self T)⟩ ω| ≤ B) :
    μ.real {ω | ε ≤ Z (Fin.last T) ω - Z ⟨0, Nat.zero_lt_succ T⟩ ω} ≤
      Real.exp (-(ε ^ 2) / (2 * B ^ 2 * (T : ℝ))) ∧
    μ.real {ω | ε ≤ Z ⟨0, Nat.zero_lt_succ T⟩ ω - Z (Fin.last T) ω} ≤
      Real.exp (-(ε ^ 2) / (2 * B ^ 2 * (T : ℝ))) := by sorry

end ModernOnlineLearning.OnlineToBatch
