-- Prove2me | Theorems.Thm_MinimaxWass_DataDep_theorem_1
-- name    : MinimaxWass.DataDep.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:12.371428+00:00
-- url     : https://prove2.me/theorems/c57e8371-99bd-4a22-a693-89a98c9d444e
-- title:
--   Theorem 1, p. 5 — two data-dependent high-probability bounds on local worst-case risk
-- statement:
--   Let $\mathcal Z$ be a bounded Polish metric space, $p\ge1$, $\varrho>0$, and $P$ a Borel probability law. Let $\mathcal F$ be a class of upper semicontinuous losses satisfying $0\le f(z)\le M$ for all $f\in\mathcal F$ and $z\in\mathcal Z$. For $n\ge1$ independent observations $Z_1,\ldots,Z_n$ from $P$, let $P_n$ be their empirical law, and let $t>0$. Then both bounds hold:
--
--   $$\mathbb P\!\left\{\exists f\in\mathcal F:R_{\varrho,p}(P,f)>\inf_{\lambda\ge0}\left[(\lambda+1)\varrho^p+\mathbb E_{P_n}\varphi_{\lambda,f}+\frac{M\sqrt{\log(\lambda+1)}}{\sqrt n}\right]+\frac{24\mathfrak C(\mathcal F)}{\sqrt n}+\frac{Mt}{\sqrt n}\right\}\le2e^{-2t^2},$$
--
--   $$\mathbb P\!\left\{\exists f\in\mathcal F:R_{\varrho,p}(P_n,f)>\inf_{\lambda\ge0}\left[(\lambda+1)\varrho^p+\mathbb E_P\varphi_{\lambda,f}+\frac{M\sqrt{\log(\lambda+1)}}{\sqrt n}\right]+\frac{24\mathfrak C(\mathcal F)}{\sqrt n}+\frac{Mt}{\sqrt n}\right\}\le2e^{-2t^2}.$$
--
--   Here $R_{\varrho,p}(Q,f)$ is the largest risk over the $p$-Wasserstein ball around $Q$, $\varphi_{\lambda,f}(z)=\sup_{z'}(f(z')-\lambda d(z,z')^p)$, and $\mathfrak C(\mathcal F)$ is the uniform-metric entropy integral. The result controls both directions of the population–empirical comparison uniformly over the loss class.
--
--   **Formalization Note** The pin $\mathfrak C(\mathcal F)<\infty$ permits conversion from an extended entropy integral to a real number; an infinite bound in the paper is vacuous. The printed minima are encoded as real infima, and probability uses the product sample law's outer measure of each event. The empirical expectation is a finite average.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, p. 5, Theorem 1; proof Appendix C.1, pp. 13–15

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-- Lee--Raginsky, Theorem 1, p. 5: both data-dependent bounds. -/
theorem theorem_1 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbounded : Bornology.IsBounded (Set.univ : Set 𝒵))
    (p ϱ M : ℝ) (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ))
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hval : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hC : entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t) :
    (sampleLaw n P)
        {ω | ∃ f ∈ ℱ,
          localRisk p ϱ P f >
            (⨅ lam : Set.Ici (0 : ℝ),
              (lam.1 + 1) * ϱ ^ p +
              (1 / (n : ℝ)) * ∑ i : Fin n, phi p lam.1 f (ω i) +
              M * Real.sqrt (Real.log (lam.1 + 1)) / Real.sqrt n) +
            24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
            M * t / Real.sqrt n} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2)) ∧
    (sampleLaw n P)
        {ω | ∃ f ∈ ℱ,
          localRisk p ϱ (empiricalPM hn ω) f >
            (⨅ lam : Set.Ici (0 : ℝ),
              (lam.1 + 1) * ϱ ^ p +
              (∫ z, phi p lam.1 f z ∂(P : Measure 𝒵)) +
              M * Real.sqrt (Real.log (lam.1 + 1)) / Real.sqrt n) +
            24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
            M * t / Real.sqrt n} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2)) := by sorry

end MinimaxWass.DataDep
