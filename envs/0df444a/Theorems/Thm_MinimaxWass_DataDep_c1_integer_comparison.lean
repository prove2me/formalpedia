-- Prove2me | Theorems.Thm_MinimaxWass_DataDep_c1_integer_comparison
-- name    : MinimaxWass.DataDep.c1_integer_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:12.015001+00:00
-- url     : https://prove2.me/theorems/7f74c92f-5d51-48e7-981e-eb6a17c0cd30
-- title:
--   Appendix C.1, p. 14 — integer-grid bound compared with the real dual infimum
-- statement:
--   Under Assumptions 1–2, fix a sample, a loss $f\in\mathcal F$, and $t>0$. With $\lambda_k=k$ and $t_k=t+\sqrt{\log k}$ for $k\ge1$,
--
--   $$\inf_{k\ge1}\left[k\varrho^p+\mathbb E_{P_n}\varphi_{k,f}+\frac{24\mathfrak C(\mathcal F)}{\sqrt n}+\frac{Mt_k}{\sqrt n}\right]\le\inf_{\lambda\ge0}\left[(\lambda+1)\varrho^p+\mathbb E_{P_n}\varphi_{\lambda,f}+\frac{24\mathfrak C(\mathcal F)}{\sqrt n}+\frac{Mt}{\sqrt n}+\frac{M\sqrt{\log(\lambda+1)}}{\sqrt n}\right].$$
--
--   This converts the grid-uniform probability estimate into the continuous-multiplier expression in Theorem 1.
--
--   **Formalization Note** The instance space is bounded and Polish, $p\ge1$, $\varrho>0$, $n\ge1$, and $\mathfrak C(\mathcal F)<\infty$. The proof's printed minima are represented as bounded-below real infima.
-- source:
--   Lee & Raginsky, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, Appendix C.1, p. 14, integer-to-real comparison display

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-- Appendix C.1, p. 14, the comparison of the integer and real infima. -/
theorem c1_integer_comparison {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbounded : Bornology.IsBounded (Set.univ : Set 𝒵))
    (p ϱ M : ℝ) (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ))
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hval : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hC : entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t)
    (ω : Fin n → 𝒵) (f : 𝒵 → ℝ) (hf : f ∈ ℱ) :
    (⨅ k : {k : ℕ // 1 ≤ k},
      (k.1 : ℝ) * ϱ ^ p +
      (1 / (n : ℝ)) * ∑ i : Fin n, phi p (k.1 : ℝ) f (ω i) +
      24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
      M * (t + Real.sqrt (Real.log (k.1 : ℝ))) / Real.sqrt n) ≤
    ⨅ lam : Set.Ici (0 : ℝ),
      (lam.1 + 1) * ϱ ^ p +
      (1 / (n : ℝ)) * ∑ i : Fin n, phi p lam.1 f (ω i) +
      24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
      M * t / Real.sqrt n +
      M * Real.sqrt (Real.log (lam.1 + 1)) / Real.sqrt n := by sorry

end MinimaxWass.DataDep
