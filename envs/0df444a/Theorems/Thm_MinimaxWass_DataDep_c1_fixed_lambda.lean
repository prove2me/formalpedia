-- Prove2me | Theorems.Thm_MinimaxWass_DataDep_c1_fixed_lambda
-- name    : MinimaxWass.DataDep.c1_fixed_lambda
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:14.313478+00:00
-- url     : https://prove2.me/theorems/90759d11-a7cb-4b86-a804-10a6a337bf85
-- title:
--   Appendix C.1, p. 14 — fixed-multiplier local-risk bound
-- statement:
--   Under Assumptions 1–2, let $Z_1,\ldots,Z_n$ be independent observations from $P$, with $n\ge1$. For each fixed $\lambda\ge0$ and $t>0$,
--
--   $$\mathbb P\left\{\exists f\in\mathcal F:\ R_{\varrho,p}(P,f)>\lambda\varrho^p+\mathbb E_{P_n}\varphi_{\lambda,f}+\frac{24\mathfrak C(\mathcal F)}{\sqrt n}+\frac{Mt}{\sqrt n}\right\}\le e^{-2t^2}.$$
--
--   This is the fixed-multiplier form of the population-to-empirical bound before the countable union over multipliers.
--
--   **Formalization Note** The instance space is bounded and Polish, $p\ge1$, $\varrho>0$, and $\mathfrak C(\mathcal F)<\infty$. Probability is the sample law's outer measure of the event. The empirical expectation is a finite sample average.
-- source:
--   Lee & Raginsky, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, Appendix C.1, p. 14, fixed-λ display

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-- Appendix C.1, p. 14, the fixed-λ high-probability display. -/
theorem c1_fixed_lambda {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbounded : Bornology.IsBounded (Set.univ : Set 𝒵))
    (p ϱ M : ℝ) (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ))
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hval : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hC : entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) (n : ℕ) (hn : 0 < n)
    (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ) (ht : 0 < t) :
    (sampleLaw n P)
      {ω | ∃ f ∈ ℱ, localRisk p ϱ P f >
        lam * ϱ ^ p +
        (1 / (n : ℝ)) * ∑ i : Fin n, phi p lam f (ω i) +
        24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
        M * t / Real.sqrt n} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2)) := by sorry

end MinimaxWass.DataDep
