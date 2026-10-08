-- Prove2me | Theorems.Thm_OnlineLearningOCO_OnlineToBatch_theorem_5_1
-- name    : OnlineLearningOCO.OnlineToBatch.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:01.163606+00:00
-- url     : https://prove2.me/theorems/ea599013-24bb-4258-ba05-b07223330cf4
-- title:
--   Theorem 5.1 — the average online loss bounds the expected risk of the converted hypothesis
-- statement:
--   Let $T\ge1$, let $\psi_0,\dots,\psi_{T-1}$ be independent examples, each with law $Q$, let $c$ be an admissible cost on $S\times\Psi$ with risk $C(w)=\mathbb E_{\psi\sim Q}[c(w,\psi)]$, and let $w_0,\dots,w_{T-1}\in S$ be the predictions of an online learner run on the losses $f_t(w)=c(w,\psi_t)$, where $w_t$ depends only on $\psi_0,\dots,\psi_{t-1}$.
--
--   1. **Randomization.** Let $\bar w = w_r$, where $r$ is uniform on $\{0,\dots,T-1\}$ and independent of the sample. Then, with the expectation over $\psi_0,\dots,\psi_{T-1}$ and $r$,
--   $$\mathbb E\big[C(\bar w)\big] = \mathbb E\Big[\frac1T\sum_{t} f_t(w_t)\Big].$$
--   2. **Averaging.** If moreover $S$ is convex, $C$ is convex on $S$, and every online loss $c(w_t,\psi_t)$ has finite expectation, then for $\bar w = \frac1T\sum_t w_t$,
--   $$\mathbb E\big[C(\bar w)\big] \le \mathbb E\Big[\frac1T\sum_{t} f_t(w_t)\Big].$$
--
--   The theorem turns any online learner into a stochastic learner whose expected risk is at most the expected average online loss.
--
--   **Formalization Note** The randomized output is modelled genuinely: the expectation on the left of part 1 is over the product of the sample law and the uniform law of $r$. Convexity of $S$ is added in part 2 so that $\bar w\in S$, where $C$ is defined. Integrability of the online losses in part 2 is added: when the expected online loss is infinite the paper's inequality holds trivially, while Lean's Bochner integral would return $0$ for it.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 188, Theorem 5.1

import Mathlib
import Definitions.Def_OnlineLearningOCO_OnlineToBatch_Setting

open MeasureTheory

namespace OnlineLearningOCO.OnlineToBatch

/-- Theorem 5.1 (Shalev-Shwartz, FnT ML 4(2) (2011), §5, p. 188).
Let `ψ₀, …, ψ_{T-1}` be i.i.d. with law `Q`, and let `w_t` be the predictions of a
non-anticipating online algorithm run on the losses `f_t = c(·, ψ_t)`.
(a) For the conversion with randomization, `w̄ = w_r` with `r` uniform on `[T]` and independent
of the sample: `𝔼_{ψ,r}[C(w̄)] = 𝔼_ψ[(1/T) ∑_t f_t(w_t)]`.
(b) If moreover `S` is convex and `C` is convex on `S`, then for the conversion with averaging,
`w̄ = (1/T) ∑_t w_t`: `𝔼[C(w̄)] ≤ 𝔼[(1/T) ∑_t f_t(w_t)]`.

Formalization Note: in (b) the online losses `c(w_t, ψ_t)` are assumed integrable (finite
expected online loss); otherwise the right side is `+∞` and the inequality has no content. -/
theorem theorem_5_1 {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ] (S : Set (EuclideanSpace ℝ (Fin d)))
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) (A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d))
    (hA : IsOnlineLearner S A)
    (T : ℕ) (hT : 0 < T) :
    (∫ p, risk Q c (randomizedOutput A p.1 p.2) ∂((sampleLaw Q T).prod (uniformIndex T)) =
        ∫ ψ, avgOnlineLoss c A ψ ∂(sampleLaw Q T)) ∧
      (Convex ℝ S → ConvexOn ℝ S (risk Q c) →
        (∀ t : Fin T, Integrable (fun ψ => c (iterate A ψ t) (ψ t)) (sampleLaw Q T)) →
        ∫ ψ, risk Q c (averageOutput A ψ) ∂(sampleLaw Q T) ≤
          ∫ ψ, avgOnlineLoss c A ψ ∂(sampleLaw Q T)) := by sorry

end OnlineLearningOCO.OnlineToBatch
