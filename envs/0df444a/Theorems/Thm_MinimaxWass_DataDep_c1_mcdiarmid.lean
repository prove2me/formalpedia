-- Prove2me | Theorems.Thm_MinimaxWass_DataDep_c1_mcdiarmid
-- name    : MinimaxWass.DataDep.c1_mcdiarmid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:30.163114+00:00
-- url     : https://prove2.me/theorems/362f297d-9f82-4814-88b0-474e2e9ee209
-- title:
--   Appendix C.1, p. 13 — McDiarmid tail for the fixed-multiplier deviation
-- statement:
--   Under Assumptions 1–2, let $\mathcal F$ be nonempty, let $Z_1,\ldots,Z_n$ be independent with law $P$, and fix $\lambda\ge0$ and $t>0$. For the deviation $X_\lambda=\sup_{f\in\mathcal F}(\mathbb E_P\varphi_{\lambda,f}-\mathbb E_{P_n}\varphi_{\lambda,f})$,
--
--   $$\mathbb P\left\{X_\lambda>\mathbb E X_\lambda+\frac{Mt}{\sqrt n}\right\}\le e^{-2t^2}.$$
--
--   This concentration estimate controls the fluctuation of the uniform deviation at a fixed dual multiplier.
--
--   **Formalization Note** The instance space is bounded and Polish, $p\ge1$, $\varrho>0$, and $n\ge1$. The assumption $\mathfrak C(\mathcal F)<\infty$ ensures the supremum is a genuine integrable random variable; the paper's bound is uninformative when the entropy integral is infinite. Probability is evaluated as outer measure of the event.
-- source:
--   Lee & Raginsky, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, Appendix C.1, p. 13, McDiarmid display

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-- Appendix C.1, p. 13, McDiarmid display for fixed λ. -/
theorem c1_mcdiarmid {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbounded : Bornology.IsBounded (Set.univ : Set 𝒵))
    (p ϱ M : ℝ) (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF : ℱ.Nonempty)
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hval : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hC : entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) (n : ℕ) (hn : 0 < n)
    (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ) (ht : 0 < t) :
    (sampleLaw n P)
      {ω | Xlam p lam P ℱ ω >
        (∫ ω', Xlam p lam P ℱ ω' ∂(sampleLaw n P)) +
        M * t / Real.sqrt n} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2)) := by sorry

end MinimaxWass.DataDep
