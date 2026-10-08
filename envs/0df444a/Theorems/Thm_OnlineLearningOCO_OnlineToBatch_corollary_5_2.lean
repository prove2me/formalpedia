-- Prove2me | Theorems.Thm_OnlineLearningOCO_OnlineToBatch_corollary_5_2
-- name    : OnlineLearningOCO.OnlineToBatch.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:02.486067+00:00
-- url     : https://prove2.me/theorems/6c370323-a161-4658-9cc1-9fa0ec6aaf88
-- title:
--   Corollary 5.2 — online-to-batch conversion: excess risk is at most the expected average regret
-- statement:
--   Let $T\ge1$, let $\psi_0,\dots,\psi_{T-1}$ be independent examples, each with law $Q$, let $c$ be an admissible cost on $S\times\Psi$ with risk $C(w)=\mathbb E_{\psi\sim Q}[c(w,\psi)]$, and let $w_0,\dots,w_{T-1}\in S$ be the predictions of an online learner run on the losses $f_t(w)=c(w,\psi_t)$, where $w_t$ depends only on $\psi_0,\dots,\psi_{t-1}$. Let $u\in S$ be any comparator.
--
--   1. **Randomization.** For $\bar w = w_r$ with $r$ uniform on $\{0,\dots,T-1\}$ and independent of the sample,
--   $$\mathbb E\big[C(\bar w)\big] - C(u) \le \mathbb E\Big[\frac1T\sum_{t}\big(f_t(w_t)-f_t(u)\big)\Big].$$
--   2. **Averaging.** If moreover $S$ is convex, $C$ is convex on $S$, and every online loss $c(w_t,\psi_t)$ has finite expectation, then the same inequality holds for $\bar w = \frac1T\sum_t w_t$.
--
--   The right-hand side is the expected regret of the online algorithm against $u$, divided by $T$. An online learner with low regret for losses of the form $c(\cdot,\psi)$ relative to $S$ therefore yields a hypothesis whose risk is close to the best risk in $S$.
--
--   **Formalization Note** "$u$ any vector" is read as $u\in S$, where $c(u,\cdot)$ is defined. The conditions of Theorem 5.1 are carried over: convexity of $S$ and integrability of the online losses are added for the averaging part, and in the randomization part the expectation is over the product of the sample law and the uniform law of $r$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 189, Corollary 5.2

import Mathlib
import Definitions.Def_OnlineLearningOCO_OnlineToBatch_Setting

open MeasureTheory

namespace OnlineLearningOCO.OnlineToBatch

/-- Corollary 5.2 (Shalev-Shwartz, FnT ML 4(2) (2011), §5, p. 189).
Under the conditions of Theorem 5.1, for every `u ∈ S`,
`𝔼[C(w̄)] − C(u) ≤ 𝔼[(1/T) ∑_t (f_t(w_t) − f_t(u))]`, where `f_t = c(·, ψ_t)`:
(a) for the conversion with randomization (expectation over the sample and `r`);
(b) for the conversion with averaging, when `S` is convex and `C` is convex on `S`.

Formalization Note: in (b) the online losses `c(w_t, ψ_t)` are assumed integrable (finite
expected online loss), as in Theorem 5.1 (b). -/
theorem corollary_5_2 {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ] (S : Set (EuclideanSpace ℝ (Fin d)))
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) (A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d))
    (hA : IsOnlineLearner S A)
    (T : ℕ) (hT : 0 < T) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ S) :
    (∫ p, risk Q c (randomizedOutput A p.1 p.2) ∂((sampleLaw Q T).prod (uniformIndex T)) -
        risk Q c u ≤ ∫ ψ, avgRegret c A ψ u ∂(sampleLaw Q T)) ∧
      (Convex ℝ S → ConvexOn ℝ S (risk Q c) →
        (∀ t : Fin T, Integrable (fun ψ => c (iterate A ψ t) (ψ t)) (sampleLaw Q T)) →
        ∫ ψ, risk Q c (averageOutput A ψ) ∂(sampleLaw Q T) - risk Q c u ≤
          ∫ ψ, avgRegret c A ψ u ∂(sampleLaw Q T)) := by sorry

end OnlineLearningOCO.OnlineToBatch
