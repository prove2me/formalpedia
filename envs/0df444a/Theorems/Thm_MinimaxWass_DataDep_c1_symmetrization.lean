-- Prove2me | Theorems.Thm_MinimaxWass_DataDep_c1_symmetrization
-- name    : MinimaxWass.DataDep.c1_symmetrization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:05.398852+00:00
-- url     : https://prove2.me/theorems/18c0a1f6-043d-481b-93c8-64a6bc22aab4
-- title:
--   Appendix C.1, p. 13 — symmetrization of the expected deviation
-- statement:
--   Under Assumptions 1–2, let $\mathcal F$ be nonempty and let $Z_1,\ldots,Z_n$ be independent with law $P$. For a fixed $\lambda\ge0$, write $X_\lambda=\sup_{f\in\mathcal F}(\mathbb E_P\varphi_{\lambda,f}-n^{-1}\sum_i\varphi_{\lambda,f}(Z_i))$. With independent uniform signs $\varepsilon_i\in\{-1,1\}$, independent of the sample,
--
--   $$\mathbb E X_\lambda\le 2\,\mathbb E\sup_{f\in\mathcal F}\frac1n\sum_{i=1}^n\varepsilon_i\varphi_{\lambda,f}(Z_i).$$
--
--   This transfers the mean uniform deviation to a Rademacher process, the input to the entropy estimate.
--
--   **Formalization Note** The sign expectation is a finite average over Boolean sign vectors. The instance space is bounded and Polish, $p\ge1$, $\varrho>0$, and $n\ge1$. The pin $\mathfrak C(\mathcal F)<\infty$ makes the expected supremum meaningful.
-- source:
--   Lee & Raginsky, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, Appendix C.1, p. 13, symmetrization display

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-- Appendix C.1, p. 13, symmetrization display. -/
theorem c1_symmetrization {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbounded : Bornology.IsBounded (Set.univ : Set 𝒵))
    (p ϱ M : ℝ) (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF : ℱ.Nonempty)
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hval : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hC : entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) (n : ℕ) (hn : 0 < n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∫ ω, Xlam p lam P ℱ ω ∂(sampleLaw n P)) ≤
      2 * rademacherSup n p lam P ℱ := by sorry

end MinimaxWass.DataDep
