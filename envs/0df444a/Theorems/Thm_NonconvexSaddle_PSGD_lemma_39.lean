-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_39
-- name    : NonconvexSaddle.PSGD.lemma_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:18:10.47782+00:00
-- url     : https://prove2.me/theorems/a133dbc7-a4c9-40af-9d7f-9e87df8806bf
-- title:
--   Lemma 39 — $\sum_i\langle u_i,X_i\rangle\le c\lambda\sum_i\|u_i\|^2\sigma_i^2+\iota/\lambda$
-- statement:
--   Let $X_1,\dots,X_n\in\mathbb R^d$ satisfy Condition 35 with respect to a filtration $(\mathcal F_i)$ and scale parameters $\sigma_i$, and let $u_1,\dots,u_n$ be random vectors with $u_i$ $\mathcal F_{i-1}$-measurable. There is an absolute constant $c>0$ such that for every $\iota>0$ and $\lambda>0$, with probability at least $1-e^{-\iota}$,
--   $$\sum_{i=1}^n\langle u_i,X_i\rangle\le c\,\lambda\sum_{i=1}^n\|u_i\|^2\sigma_i^2+\frac{\iota}{\lambda}.$$
--
--   In Appendix B this controls the cross term $-\eta\sum_i\langle\nabla f(x_i),\tilde\zeta_i\rangle$ of the descent lemma, where the predictable vectors are the gradients along the run.
--
--   **Formalization Note** The absolute constant is quantified before every other object (the page writes "for any $\iota>0$, $\lambda>0$, there exists absolute constant $c$"; an absolute constant does not depend on them).
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 31, Lemma 39

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting
import Definitions.Def_NonconvexSaddle_PSGD_Condition35

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 39 (arXiv:1902.04811v2, App. C, p. 31). -/
theorem lemma_39 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (Ω : Type) [m : MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m) (n : ℕ) (X : ℕ → Ω → E d)
      (σ : ℕ → Ω → ℝ) (u : ℕ → Ω → E d),
      Condition35 μ ℱ n X σ → (∀ i ∈ Finset.Icc 1 n, StronglyMeasurable[ℱ (i - 1)] (u i)) →
      ∀ ι lam : ℝ, 0 < ι → 0 < lam →
      ENNReal.ofReal (1 - Real.exp (-ι)) ≤
        μ {ω | ∑ i ∈ Finset.Icc 1 n, ⟪u i ω, X i ω⟫ ≤
          c * lam * ∑ i ∈ Finset.Icc 1 n, ‖u i ω‖ ^ 2 * σ i ω ^ 2 + ι / lam} := by sorry

end NonconvexSaddle.PSGD
