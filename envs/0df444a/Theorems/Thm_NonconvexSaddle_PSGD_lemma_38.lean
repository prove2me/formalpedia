-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_38
-- name    : NonconvexSaddle.PSGD.lemma_38
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:18:01.878166+00:00
-- url     : https://prove2.me/theorems/6f218c78-d777-4857-88d1-16fecee7f07b
-- title:
--   Lemma 38 — $\sum_i\|X_i\|^2\le c\,\sigma^2(n+\iota)$ for norm-subGaussian martingale differences
-- statement:
--   Let $X_1,\dots,X_n\in\mathbb R^d$ satisfy Condition 35 with the same fixed scale parameter $\sigma_1=\dots=\sigma_n=\sigma$. There is an absolute constant $c>0$ (independent of $d$, $n$, $\sigma$, the probability space and $\iota$) such that for every $\iota>0$, with probability at least $1-e^{-\iota}$,
--   $$\sum_{i=1}^n\|X_i\|^2\le c\,\sigma^2\,(n+\iota).$$
--
--   In Appendix B this bounds the accumulated squared noise $\sum_i\|\tilde\zeta_i\|^2$ in the descent lemma.
--
--   **Formalization Note** The absolute constant is quantified before every other object, so it cannot depend on the instance.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 31, Lemma 38

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting
import Definitions.Def_NonconvexSaddle_PSGD_Condition35

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 38 (arXiv:1902.04811v2, App. C, p. 31). -/
theorem lemma_38 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (Ω : Type) [m : MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m) (n : ℕ) (X : ℕ → Ω → E d) (σ : ℝ),
      Condition35 μ ℱ n X (fun _ _ => σ) → ∀ ι : ℝ, 0 < ι →
      ENNReal.ofReal (1 - Real.exp (-ι)) ≤
        μ {ω | ∑ i ∈ Finset.Icc 1 n, ‖X i ω‖ ^ 2 ≤ c * σ ^ 2 * ((n : ℝ) + ι)} := by sorry

end NonconvexSaddle.PSGD
