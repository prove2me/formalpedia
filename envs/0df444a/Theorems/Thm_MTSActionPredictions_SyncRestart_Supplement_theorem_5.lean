-- Prove2me | Theorems.Thm_MTSActionPredictions_SyncRestart_Supplement_theorem_5
-- name    : MTSActionPredictions.SyncRestart.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:29:43.488196+00:00
-- url     : https://prove2.me/theorems/8102eb52-2c27-4c0a-a7e1-7444b3236f8f
-- title:
--   Theorem 5 — diameter-independent combination: $\mathbb E[\mathrm{Comb}]\le O(1+\log V)\min_i\{a_i\mathrm{OFF}+b_i\eta\}$
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $(M,d)$ be a metric space with start state $x_0$ and a set of valid service cost functions that is closed under ball restriction: for every valid $c$ and every $r\ge0$ the function $c^{\le r}$ (equal to $c$ on the closed ball of radius $r$ around $x_0$ and $\infty$ outside) is valid. Let $\mathrm{Alg}_1,\dots,\mathrm{Alg}_m$ be randomized online algorithms with action predictions started at $x_0$ (with measurable costs). Let $a_1,\dots,a_m\ge1$ be known and let $V\ge1$ satisfy
--   $$\sum_{i=1}^m V^{-a_i}\le1.\qquad(2)$$
--   Then there is a randomized online algorithm $\mathrm{Comb}$, constructed from the algorithms, the $a_i$ and $V$ only, such that for all (possibly unknown) $b_1,\dots,b_m\ge0$ with
--   $$\mathbb E[\mathrm{Alg}_i]\le a_i\,\mathrm{OFF}+b_i\,\eta\qquad(1)$$
--   for every valid input, every offline solution $\mathrm{OFF}$ and every $i$, on every valid input and for every offline solution
--   $$\mathbb E[\mathrm{Comb}]\le C\,(1+\ln V)\cdot\min_i\{a_i\,\mathrm{OFF}+b_i\,\eta\}.\qquad(3)$$
--
--   The guarantee is independent of the diameter of $M$, of the number $m$ of algorithms and of the horizon, and has no additive constant; it is the combination step used for Euclidean convex body chasing (Theorem 4).
--
--   Differences from the source:
--   - reading: O(1 + log V) → C(1 + ln V) with one universal C > 0, uniform over the metric space, model, family, a, b, V, input and comparator; reason: the source’s O hides an absolute constant; its proof tracks every factor
--   - reading: the property for c^{≤r} with r unspecified → closure under c^{≤r} for every real r ≥ 0; reason: r is a radius; the weaker hypothesis (no r < 0) makes the statement at least as strong
--   - reading: known a_i, possibly unknown b_i → Comb is chosen before b is quantified (∃ Comb ∀ b), from the algorithms, their seed law, a and V; reason: this is the source’s requirement that Comb not depend on the b_i
--   - encoding: randomized algorithms with action predictions and their expectations → seed-indexed rules on one common probability space, with costs and the distance from the final state to any fixed state measurable in the seed (PScalarMeasurable, as in the base ScalarMeasurable); E[Alg_i] as the lower Lebesgue integral, E[Comb] as the upper expectation over an existential probability space; reason: a family on different spaces lives on their product; measurability only excludes inputs where E[Alg_i] is undefined; the upper expectation equals E when measurable and is never smaller
--   - encoding: Alg_1, …, Alg_m with m ≥ 1 → any m : ℕ; reason: for m = 0 the minimum is ∞ and the bound holds trivially
--   - encoding: costs, OFF and η in [0, ∞] → ENNReal with the published base cost and prediction error, OFF any trajectory with O_0 = x_0; reason: same quantities, infinities retained
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; Theorem 5, PDF pp. 4–5 / printed pp. 3–4, restated PDF p. 28 / printed p. 27, equations (1)–(3); proof PDF pp. 28–30 / printed pp. 27–29

import Definitions.Def_MTSActionPredictions_SyncRestart_Supplement_Predictions

open scoped ENNReal BigOperators
open MeasureTheory

namespace MTSActionPredictions.SyncRestart.Supplement

open MTSActionPredictions.SyncRestart

universe u v

/-- Theorem 5, PDF 4–5 and 28 / printed 3–4 and 27: there is a universal constant `C` such that for
every problem with an MTS formulation whose valid tasks are closed under ball restriction around the
start `x₀`, every finite family of randomized algorithms with action predictions `Alg_1, …, Alg_m`,
every known `a_i ≥ 1` and every `V ≥ 1` with `∑_i V^{-a_i} ≤ 1`, there is a randomized online
algorithm `Comb` (built without knowledge of the `b_i`) such that for all `b_i ≥ 0` satisfying
`E[Alg_i] ≤ a_i OFF + b_i η` on every input and for every offline solution, on every input and for
every offline solution
`E[Comb] ≤ C (1 + ln V) · min_i {a_i OFF + b_i η}`. -/
theorem theorem_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [MetricSpace M] (model : Model M) (x₀ : M), RestrictionClosed model x₀ →
      ∀ {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (m : ℕ) (A : Fin m → PRule Ω M), (∀ i, PScalarMeasurable model x₀ (A i)) →
      ∀ (a : Fin m → ℝ), (∀ i, 1 ≤ a i) →
      ∀ V : ℝ, 1 ≤ V → ∑ i, V ^ (-(a i)) ≤ 1 →
        ∃ (Ω' : Type v) (_ : MeasurableSpace Ω') (μ' : Measure Ω'), IsProbabilityMeasure μ' ∧
          ∃ Comb : PRule Ω' M,
            ∀ b : Fin m → ℝ, (∀ i, 0 ≤ b i) →
              (∀ i q, ValidTasks model (tasks q) → ∀ O : ℕ → M, O 0 = x₀ →
                ∫⁻ ω, pcost (A i) ω x₀ q ∂μ ≤
                  ENNReal.ofReal (a i) * trajectoryCost (tasks q) O +
                  ENNReal.ofReal (b i) * perror x₀ q O) →
              ∀ q, ValidTasks model (tasks q) → ∀ O : ℕ → M, O 0 = x₀ →
                upperExp μ' (fun ω => pcost Comb ω x₀ q) ≤
                  ENNReal.ofReal (C * (1 + Real.log V)) *
                    ⨅ i, (ENNReal.ofReal (a i) * trajectoryCost (tasks q) O +
                      ENNReal.ofReal (b i) * perror x₀ q O) := by sorry

end MTSActionPredictions.SyncRestart.Supplement
