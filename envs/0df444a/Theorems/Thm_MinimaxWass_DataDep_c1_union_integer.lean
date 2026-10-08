-- Prove2me | Theorems.Thm_MinimaxWass_DataDep_c1_union_integer
-- name    : MinimaxWass.DataDep.c1_union_integer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:12.317683+00:00
-- url     : https://prove2.me/theorems/2943ea2b-99a4-47ac-ba7c-aee5bf61d9f3
-- title:
--   Appendix C.1, p. 14 — union bound over positive integer multipliers
-- statement:
--   Under Assumptions 1–2, set $\lambda_k=k$ and $t_k=t+\sqrt{\log k}$ for integers $k\ge1$ and $t>0$. For $n\ge1$ independent observations from $P$,
--
--   $$\mathbb P\left\{\exists f\in\mathcal F:\ R_{\varrho,p}(P,f)>\inf_{k\ge1}\left[k\varrho^p+\mathbb E_{P_n}\varphi_{k,f}+\frac{24\mathfrak C(\mathcal F)}{\sqrt n}+\frac{Mt_k}{\sqrt n}\right]\right\}\le2e^{-2t^2}.$$
--
--   The countable union makes the fixed-multiplier estimate simultaneous over the integer grid.
--
--   **Formalization Note** The instance space is bounded and Polish, $p\ge1$, $\varrho>0$, and $\mathfrak C(\mathcal F)<\infty$. The printed minimum is an infimum over positive integers; the event uses outer measure.
-- source:
--   Lee & Raginsky, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, Appendix C.1, p. 14, union-bound display

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-- Appendix C.1, p. 14, the union bound over positive integer dual multipliers. -/
theorem c1_union_integer {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
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
      {ω | ∃ f ∈ ℱ, localRisk p ϱ P f >
        ⨅ k : {k : ℕ // 1 ≤ k},
          (k.1 : ℝ) * ϱ ^ p +
          (1 / (n : ℝ)) * ∑ i : Fin n, phi p (k.1 : ℝ) f (ω i) +
          24 * (entropyIntegral ℱ).toReal / Real.sqrt n +
          M * (t + Real.sqrt (Real.log (k.1 : ℝ))) / Real.sqrt n} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2)) := by sorry

end MinimaxWass.DataDep
