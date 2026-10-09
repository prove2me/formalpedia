-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_37
-- name    : NonconvexSaddle.PSGD.lemma_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:17:16.816385+00:00
-- url     : https://prove2.me/theorems/e54bab97-9fb8-4cae-b09d-a611c9f2a494
-- title:
--   Lemma 37 — norm-subGaussian concentration with random scale parameters
-- statement:
--   Let $X_1,\dots,X_n\in\mathbb R^d$ satisfy Condition 35, with possibly random scale parameters $\sigma_i$. There is an absolute constant $c>0$ such that for all $\iota>0$ and $B>b>0$, with probability at least $1-2d\,(\log(B/b)+1)\,e^{-\iota}$,
--   $$\sum_{i=1}^n\sigma_i^2\ge B\qquad\text{or}\qquad \Big\|\sum_{i=1}^nX_i\Big\|\le c\,\sqrt{\max\Big\{\sum_{i=1}^n\sigma_i^2,\ b\Big\}\cdot\iota}.$$
--
--   This extends Lemma 36 to scale parameters that are only predictable; in Appendix B it handles the stochastic-gradient term when Assumption C makes the noise scale proportional to $\|\hat x_\tau\|$.
--
--   **Formalization Note** The page prints the failure probability $2d\log(B/b)\,e^{-\iota}$. That statement is false when $B/b$ is close to $1$: the failure bound tends to $0$ while the event can fail with fixed positive probability (one Gaussian summand with $\sum\sigma_i^2=b$). The statement here uses $2d(\log(B/b)+1)e^{-\iota}$, the bound a peeling argument over $\lceil\log(B/b)\rceil$ scales gives. The constant comes before every other object.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 31, Lemma 37 (failure probability corrected, see the Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting
import Definitions.Def_NonconvexSaddle_PSGD_Condition35

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 37 (arXiv:1902.04811v2, App. C, p. 31), with random scale parameters `σ_i`. The
failure probability is `2d(log(B/b) + 1)e^{−ι}`; the page prints `2d log(B/b) e^{−ι}`, which is
false when `B/b` is close to `1` (see the Formalization Note). -/
theorem lemma_37 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (Ω : Type) [m : MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m) (n : ℕ) (X : ℕ → Ω → E d)
      (σ : ℕ → Ω → ℝ),
      Condition35 μ ℱ n X σ → ∀ ι B b : ℝ, 0 < ι → 0 < b → b < B →
      ENNReal.ofReal (1 - 2 * d * (Real.log (B / b) + 1) * Real.exp (-ι)) ≤
        μ {ω | B ≤ ∑ i ∈ Finset.Icc 1 n, σ i ω ^ 2 ∨
          ‖∑ i ∈ Finset.Icc 1 n, X i ω‖ ≤
            c * Real.sqrt (max (∑ i ∈ Finset.Icc 1 n, σ i ω ^ 2) b * ι)} := by sorry

end NonconvexSaddle.PSGD
