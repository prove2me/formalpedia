-- Prove2me | Theorems.Thm_KMNewsvendor_optional_skipping_slln
-- name    : KMNewsvendor.optional_skipping_slln
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T02:49:28.468094+00:00
-- url     : https://prove2.me/theorems/4349709a-22f4-4429-8edb-31f65faef025
-- title:
--   Lemma 1 — strong law of large numbers along a predictably selected subsequence
-- statement:
--   Let $D_1,D_2,\dots$ be independent real random variables, all distributed like $D$, and let $\mathcal F_t=\sigma(D_1,\dots,D_t)$ ($\mathcal F_0$ trivial). Let $\xi_1,\xi_2,\dots\in\{0,1\}$ be selection indicators such that each $\xi_t$ is $\mathcal F_{t-1}$-measurable, i.e. a deterministic measurable function of $D_1,\dots,D_{t-1}$, and such that almost surely $\xi_t=1$ for infinitely many $t$. Let $f:\mathbb R\to\mathbb R$ be measurable with $f(D)$ integrable. Then, almost surely,
--   $$\lim_{T\to\infty}\frac{\sum_{t=1}^{T}\xi_t\,f(D_t)}{\sum_{t=1}^{T}\xi_t}=E[f(D)].$$
--
--   The subsequence of selected demands is chosen adaptively, after seeing the earlier demands, and the strong law still holds along it. This is the probabilistic engine of the paper: the censoring decisions of an inventory policy are exactly such predictable selections.
--
--   **Formalization Note** Lean's index $t$ is the source's $t+1$; `ξ t` is a Boolean given by a measurable function of `D 0, …, D (t-1)` (for $t=0$, a constant). "$P[\sum_t\xi_t=\infty]=1$" is "almost surely, frequently `ξ t = true`". The source's hypothesis "$E[f(D)]<\infty$" is formalized as integrability of $f(D)$, which makes $E[f(D)]$ a finite real number. For the finitely many $T$ with an empty selection the Lean quotient is $0/0=0$, which does not affect the limit.
-- source:
--   Huh, Levi, Rusmevichientong, Orlin, Adaptive Data-Driven Inventory Control with Censored Demand Based on Kaplan-Meier Estimator, Oper. Res. 59(4) (2011), doi:10.1287/opre.1100.0906, p. 934, Lemma 1

import Mathlib
open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace KMNewsvendor

/-- Lemma 1 (p. 934): the strong law of large numbers along a predictably selected subsequence.
`ξ t` (Lean period `t`, the paper's `ξ_{t+1}`) is a deterministic measurable function of
the demands `D i`, `i < t`; infinitely many periods are selected almost surely; `f (D)` is integrable. -/
theorem optional_skipping_slln {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ t, Measurable (D t)) (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧ ξ t = fun ω => g (fun i => D i ω))
    (hinf : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ξ t ω = true)
    (f : ℝ → ℝ) (hf : Measurable f) (hint : Integrable (fun ω => f (D 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ =>
        (∑ t ∈ range T, if ξ t ω = true then f (D t ω) else 0) /
          (((range T).filter (fun t => ξ t ω = true)).card : ℝ))
      atTop (𝓝 (∫ ω, f (D 0 ω) ∂μ)) := by sorry

end KMNewsvendor
