-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_lemma_36
-- name    : NonconvexSaddle.PSGD.lemma_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:17:25.973777+00:00
-- url     : https://prove2.me/theorems/d196f95b-759e-40db-b944-89db7c60e444
-- title:
--   Lemma 36 — Hoeffding-type inequality for norm-subGaussian vectors
-- statement:
--   Let $X_1,\dots,X_n\in\mathbb R^d$ satisfy Condition 35 with fixed (deterministic) scale parameters $\sigma_1,\dots,\sigma_n$. There is an absolute constant $c>0$ such that for every $\iota>0$, with probability at least $1-2d\,e^{-\iota}$,
--   $$\Big\|\sum_{i=1}^n X_i\Big\|\le c\,\sqrt{\sum_{i=1}^n\sigma_i^2\cdot\iota}.$$
--
--   This vector Hoeffding bound is tight up to the $\log d$ factor hidden in the failure probability. In Appendix B it bounds the accumulated noise in the localization lemma (Lemma 24) and the stochastic-gradient term $q_{sg}$ of the coupling argument.
--
--   **Formalization Note** The absolute constant is quantified before every other object, although the page writes "for any $\iota>0$, there exists an absolute constant $c$": an absolute constant cannot depend on $\iota$.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 30, Lemma 36

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting
import Definitions.Def_NonconvexSaddle_PSGD_Condition35

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- Lemma 36 (Hoeffding-type inequality for norm-subGaussian vectors; arXiv:1902.04811v2,
App. C, p. 30). The scale parameters `σ_i = s i` are fixed (deterministic). -/
theorem lemma_36 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (Ω : Type) [m : MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m) (n : ℕ) (X : ℕ → Ω → E d) (s : ℕ → ℝ),
      Condition35 μ ℱ n X (fun i _ => s i) → ∀ ι : ℝ, 0 < ι →
      ENNReal.ofReal (1 - 2 * d * Real.exp (-ι)) ≤
        μ {ω | ‖∑ i ∈ Finset.Icc 1 n, X i ω‖ ≤
          c * Real.sqrt ((∑ i ∈ Finset.Icc 1 n, s i ^ 2) * ι)} := by sorry

end NonconvexSaddle.PSGD
