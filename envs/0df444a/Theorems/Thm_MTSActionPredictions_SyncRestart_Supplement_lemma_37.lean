-- Prove2me | Theorems.Thm_MTSActionPredictions_SyncRestart_Supplement_lemma_37
-- name    : MTSActionPredictions.SyncRestart.Supplement.lemma_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:29:15.417199+00:00
-- url     : https://prove2.me/theorems/9fae1c0b-fd6c-49de-b302-b16a5d61d064
-- title:
--   Lemma 37 — combining online algorithms confined to balls of different radii, equation (23)
-- statement:
--   Let $(M,d)$ be a metric space with start state $x_0$ and a set of valid service cost functions. Let $\mathrm{Alg}_1,\dots,\mathrm{Alg}_m$ be deterministic online algorithms started at $x_0$; write $x^i_t$ for the state of $\mathrm{Alg}_i$ at time $t$ and $\mathrm{Alg}_i$ also for its total cost. Let $R_1,\dots,R_m>0$ with $d(x^i_t,x_0)\le R_i$ for every $i$, every valid input and every time $t$, and let $\pi_1,\dots,\pi_m>0$ with $\sum_i\pi_i=1$. Then there is a randomized online algorithm $\mathrm{AlgComb}$ whose expected cost on every valid input is at most
--   $$\mathbb E[\mathrm{AlgComb}]\le\min_{1\le i\le m}\Big\{3\,\mathrm{Alg}_i+3R_i\ln\frac1{\pi_i}\Big\}+2\sum_{i=1}^m\pi_iR_i.\qquad(23)$$
--
--   The radius-weighted penalty sits inside the minimum and the last sum outside it; the bound has no dependence on the diameter of $M$ beyond the radii. It is the combination step behind Theorem 5.
--
--   **Formalization Note** Costs may be $+\infty$. The expectation of $\mathrm{AlgComb}$ is the upper expectation over its own randomness (equal to the ordinary expectation when its cost is measurable).
--
--   Differences from the source:
--   - reading: online algorithms Alg_1, …, Alg_m with positions x^i_t and costs Alg_i (not expectations) in (23) → deterministic online algorithms (one-point seed space); reason: the proof fixes each x^i_t as a function of the input; the proof of Theorem 5 applies the lemma conditionally on the constituents’ randomness
--   - reading: d(x^i_t, x_0) ≤ R_i for each i and time t → for every valid input and every time 0 ≤ t ≤ T of that input; reason: the positions x^i_t exist only on an input; the bound is assumed on exactly the inputs on which the conclusion is claimed
--   - generalization: online algorithms for a problem with an MTS formulation → online algorithms that may also see an action prediction revealed with each request; reason: the proof of Theorem 5 applies the lemma to algorithms with predictions; algorithms without predictions are the special case that ignores them, and a combiner fed a fixed prediction is a combiner without predictions
--   - encoding: expected cost of AlgComb in [0, ∞] → upper expectation (infimum of expectations of measurable majorants) over an existential probability space; reason: equals the expectation when the cost is measurable and is never smaller
--   - encoding: log → Real.log (natural logarithm); reason: the proof uses exp and log as inverse functions
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; Lemma 37, PDF pp. 25–26 / printed pp. 24–25, equation (23); proof PDF pp. 26–28 / printed pp. 25–27

import Definitions.Def_MTSActionPredictions_SyncRestart_Supplement_Predictions

open scoped ENNReal BigOperators
open MeasureTheory

namespace MTSActionPredictions.SyncRestart.Supplement

open MTSActionPredictions.SyncRestart

universe u

/-- Lemma 37, PDF 25–26 / printed 24–25, equation (23): for deterministic online algorithms
`Alg_1, …, Alg_m` from the common start `x₀` whose states stay within distance `R_i > 0` of `x₀`,
and prior weights `π_i > 0` summing to one, some randomized online algorithm `AlgComb` has, on every
valid input, expected cost at most
`min_i {3 Alg_i + 3 R_i ln(1/π_i)} + 2 ∑_i π_i R_i`. -/
theorem lemma_37 {M : Type u} [MetricSpace M] (model : Model M) (x₀ : M) (m : ℕ)
    (A : Fin m → PRule Unit M) (R : Fin m → ℝ) (hR : ∀ i, 0 < R i)
    (hball : ∀ i q, ValidTasks model (tasks q) → ∀ t ≤ q.length,
      dist (ptraj (A i) () x₀ q t) x₀ ≤ R i)
    (π : Fin m → ℝ) (hπ : ∀ i, 0 < π i) (hπ1 : ∑ i, π i = 1) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ Comb : PRule Ω M, ∀ q, ValidTasks model (tasks q) →
        upperExp μ (fun ω => pcost Comb ω x₀ q) ≤
          (⨅ i, (3 * pcost (A i) () x₀ q + ENNReal.ofReal (3 * R i * Real.log (1 / π i)))) +
          ENNReal.ofReal (2 * ∑ i, π i * R i) := by sorry

end MTSActionPredictions.SyncRestart.Supplement
