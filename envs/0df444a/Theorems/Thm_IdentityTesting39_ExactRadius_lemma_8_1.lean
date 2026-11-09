-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_lemma_8_1
-- name    : IdentityTesting39.ExactRadius.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:16.293779+00:00
-- url     : https://prove2.me/theorems/0b4742f1-2f7e-45f7-aaa9-91d28592d4dd
-- title:
--   Lemma 8.1 — strict weighted-Bernoulli anticoncentration
-- statement:
--   On a probability space, let $(B_i)$ be a finite independent family of measurable $\{0,1\}$-valued variables, with success probabilities $p_i$, and let $a_i>0$. Suppose the variance of $S=\sum_i a_iB_i$ is positive. Both following assertions hold:
--
--   $$\bigl(\forall i,\ p_i\le3/4\bigr)\ \Longrightarrow\ \Pr\!\left(S<\sum_i a_ip_i\right)\ge1/152,$$
--
--   $$\bigl(\forall i,\ p_i\ge1/4\bigr)\ \Longrightarrow\ \Pr\!\left(S>\sum_i a_ip_i\right)\ge1/152.$$
--
--   The events are strict even when the mean is an atom. The two conclusions implement both the main statement and its equivalently sentence; they supply the strict far event in the deficit-prior construction.
--
--   Differences from the source:
--   - reading: Σ_i with no explicit index range → a finite family of Bernoulli variables; reason: the proof orders the weights and removes a finite prefix, and the only application is finite
--   - encoding: Bernoulli variables with probabilities p_i → measurable real variables almost surely in {0,1}, with event probabilities p_i and iIndepFun; reason: this is the same Bernoulli law on an arbitrary probability space
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.11, Lemma 8.1, display (14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace IdentityTesting39.ExactRadius

/-- Lemma 8.1 and its equivalently clause, printed p.11 / PDF p.12; both events are strict. -/
theorem lemma_8_1 {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : ι → Ω → ℝ) (p a : ι → ℝ)
    (hB : ∀ i, Measurable (B i)) (hvalues : ∀ i, ∀ᵐ ω ∂μ, B i ω = 0 ∨ B i ω = 1)
    (hp : ∀ i, (μ {ω | B i ω = 1}).toReal = p i)
    (hind : iIndepFun B μ) (ha : ∀ i, 0 < a i)
    (hvar : 0 < variance (fun ω => ∑ i, a i*B i ω) μ) :
    ((∀ i, p i ≤ 3/4) →
      ENNReal.ofReal (1/152 : ℝ) ≤ μ {ω | (∑ i, a i*B i ω) < ∑ i, a i*p i}) ∧
    ((∀ i, 1/4 ≤ p i) →
      ENNReal.ofReal (1/152 : ℝ) ≤ μ {ω | (∑ i, a i*p i) < ∑ i, a i*B i ω}) := by sorry

end IdentityTesting39.ExactRadius
