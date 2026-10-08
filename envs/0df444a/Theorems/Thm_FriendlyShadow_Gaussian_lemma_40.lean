-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_40
-- name    : FriendlyShadow.Gaussian.lemma_40
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:53:21.745483+00:00
-- url     : https://prove2.me/theorems/87f42e16-2242-487a-8614-01b74956ad0c
-- title:
--   Lemma 40, p. 31 — E[X²]/E[|X|] ≥ (|µ| + τ)/2 for E[X] = µ, Var(X) = τ²
-- statement:
--   Let $X$ be a real random variable with finite second moment, $\mathbb E[X]=\mu$ and $\operatorname{Var}(X)=\tau^2$, $\tau\ge0$. Then
--   $$\frac{\mathbb E[X^2]}{\mathbb E[|X|]}\ \ge\ \frac{|\mu|+\tau}{2},\qquad\text{stated as}\qquad \frac{|\mu|+\tau}{2}\,\mathbb E[|X|]\le\mathbb E[X^2].$$
--
--   This elementary moment inequality is the last step of the height bound (Lemma 41).
--
--   **Formalization Note** The multiplied-out form needs no assumption $\mathbb E|X|>0$, and is equivalent to the page's ratio whenever the ratio is defined. Finite second moment (`MemLp X 2`) is the condition under which the variance is defined.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 40, p. 31

import Mathlib

open MeasureTheory

namespace FriendlyShadow.Gaussian

/-- Lemma 40 (p. 31), cross-multiplied. A real random variable `X` with finite second moment,
mean `E[X]` and variance `τ²` (`τ ≥ 0`) satisfies `(|E X| + τ)/2 · E|X| ≤ E[X²]`. -/
theorem lemma_40 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (τ : ℝ) (hτ : 0 ≤ τ)
    (hvar : ProbabilityTheory.variance X P = τ ^ 2) :
    (|∫ ω, X ω ∂P| + τ) / 2 * ∫ ω, |X ω| ∂P ≤ ∫ ω, X ω ^ 2 ∂P := by sorry

end FriendlyShadow.Gaussian
