-- Prove2me | Theorems.Thm_IntervalToDynamic_Supplement_theorem_8
-- name    : IntervalToDynamic.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:41:19.17036+00:00
-- url     : https://prove2.me/theorems/b6e2d242-d082-4c0a-8e29-36585b7c7c66
-- title:
--   Theorem 8 — dynamic-regret lower bounds for $k$-th difference variation
-- statement:
--   Fix $k\ge1$. There are constants $c_{k,\rm lin},c_{k,\rm sq}>0$ depending only on $k$ such that for every positive horizon, every budget $0\le\tau_k\le T^k$, and every possibly randomized nonanticipating learner on $[-1,1]$, there are two separate random hard constructions:
--
--   1. For linear losses $f_t(x)=\varepsilon_tx$, $\varepsilon_t\in\{-1,1\}$, there is an $[-1,1]$-valued comparator path with $P_{T,k}\le\tau_k$ and
--      $$\mathbb E[\operatorname{D-Reg}_T]\ge c_{k,\rm lin}\bigl(\sqrt T+\tau_k^{1/(2k)}\sqrt T\bigr).$$
--   2. For squared losses $f_t(x)=(x-\varepsilon_t)^2$, there is such a path with
--      $$\mathbb E[\operatorname{D-Reg}_T]\ge c_{k,\rm sq}\bigl(1+\tau_k^{2/(2k+1)}T^{1/(2k+1)}\bigr).$$
--
--   The expectation is over the construction and the learner's independent seed. The statement also includes the exact $1$-Lipschitz linear bound and the $4$-Lipschitz, $2$-strongly convex and $1/8$-exp-concave properties of squared loss on $[-1,1]$.
--
--   Differences from the source:
--   - encoding: an arbitrary randomized nonanticipating learner → an arbitrary measurable seed space with a probability law and a measurable history-map action, integrated independently against a finite hard-construction law; reason: one private seed represents all learner randomization and the proof's signs and responses have finite support
--   - encoding: expected regret → a Bochner integral together with an explicit integrability clause for each hard construction; reason: Lean otherwise assigns the junk value zero to a nonintegrable real-valued integral
--   - encoding: $\Omega_k$ → positive constants depending only on $k$, quantified before the horizon, budget and learner; reason: this is the uniform dependence asserted by the subscripted asymptotic notation
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 8, p.12 (PDF p.14); proof, pp.39–41 (PDF pp.41–43)

import Mathlib
import Definitions.Def_IntervalToDynamic_Supplement_HigherVariation
import Definitions.Def_IntervalToDynamic_Supplement_RandomizedLearner
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn

open MeasureTheory
open ModernOnlineLearning.Dynamic (dynamicRegret)

namespace IntervalToDynamic.Supplement

/-- Theorem 8 (dynamic-regret lower bounds for `k`-th difference variation),
Wang--Zhao--Zhou, *On the Relation Between Interval Regret and Dynamic Regret*,
arXiv:2609.34423, p.12 (PDF p.14).

The constants depend only on fixed `k` and are chosen before the horizon, variation budget, seed
space, seed law, and learner. The two existential hard distributions are separate. Their product
with the learner's private seed law makes both sources of randomness part of the expectation. -/
theorem theorem_8 (k : ℕ) (hk : 1 ≤ k) :
    ∃ cLin cSq : ℝ, 0 < cLin ∧ 0 < cSq ∧
    ∀ (T : ℕ), 1 ≤ T → ∀ tau : ℝ,
      0 ≤ tau → tau ≤ (T : ℝ) ^ k →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (L : RandomizedLearner Ω),
      (∃ (ν : Measure (Fin (2 * T) → Bool)), IsProbabilityMeasure ν ∧
        ∃ (eps : (Fin (2 * T) → Bool) → ℕ → ℝ)
          (u : (Fin (2 * T) → Bool) → ℕ → ℝ),
          (∀ ξ t, t ∈ Finset.Icc 1 T → eps ξ t = -1 ∨ eps ξ t = 1) ∧
          (∀ ξ t, t ∈ Finset.Icc 1 T → u ξ t ∈ Set.Icc (-1 : ℝ) 1) ∧
          (∀ ξ, normalizedVariation (u ξ) T k ≤ tau) ∧
          (∀ ξ t, t ∈ Finset.Icc 1 T → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
            ∀ y ∈ Set.Icc (-1 : ℝ) 1,
              |eps ξ t * x - eps ξ t * y| ≤ |x - y|) ∧
          Integrable (fun q : (Fin (2 * T) → Bool) × Ω =>
            dynamicRegret (fun t x => eps q.1 t * x)
              (randomizedDecisions L q.2 (fun t x => eps q.1 t * x)) (u q.1) T) (ν.prod μ) ∧
          cLin * (Real.sqrt T + tau ^ (1 / (2 * k) : ℝ) * Real.sqrt T) ≤
            expectedDynamicRegret ν μ L (fun ξ t x => eps ξ t * x) u T) ∧
      (∃ (ν : Measure (Fin (2 * T) → Bool)), IsProbabilityMeasure ν ∧
        ∃ (eps : (Fin (2 * T) → Bool) → ℕ → ℝ)
          (u : (Fin (2 * T) → Bool) → ℕ → ℝ),
          (∀ ξ t, t ∈ Finset.Icc 1 T → eps ξ t = -1 ∨ eps ξ t = 1) ∧
          (∀ ξ t, t ∈ Finset.Icc 1 T → u ξ t ∈ Set.Icc (-1 : ℝ) 1) ∧
          (∀ ξ, normalizedVariation (u ξ) T k ≤ tau) ∧
          (∀ ξ t, t ∈ Finset.Icc 1 T →
            (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
              |(x - eps ξ t) ^ 2 - (y - eps ξ t) ^ 2| ≤ 4 * |x - y|) ∧
            StrongConvexOn (Set.Icc (-1 : ℝ) 1) 2 (fun x => (x - eps ξ t) ^ 2) ∧
            ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1)
              (fun x => Real.exp (-((1 / 8 : ℝ) * (x - eps ξ t) ^ 2)))) ∧
          Integrable (fun q : (Fin (2 * T) → Bool) × Ω =>
            dynamicRegret (fun t x => (x - eps q.1 t) ^ 2)
              (randomizedDecisions L q.2 (fun t x => (x - eps q.1 t) ^ 2)) (u q.1) T) (ν.prod μ) ∧
          cSq * (1 + tau ^ ((2 : ℝ) / (2 * k + 1)) *
            (T : ℝ) ^ ((1 : ℝ) / (2 * k + 1))) ≤
            expectedDynamicRegret ν μ L (fun ξ t x => (x - eps ξ t) ^ 2) u T) := by sorry

end IntervalToDynamic.Supplement
