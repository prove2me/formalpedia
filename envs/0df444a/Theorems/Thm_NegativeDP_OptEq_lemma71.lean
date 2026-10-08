-- Prove2me | Theorems.Thm_NegativeDP_OptEq_lemma71
-- name    : NegativeDP.OptEq.lemma71
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:13.102163+00:00
-- url     : https://prove2.me/theorems/72fa3e7a-fcfc-42c9-9f45-6b6813abb5e8
-- title:
--   Lemma 7.1 — $(s,\nu)\mapsto \nu u(s,\cdot)$ is measurable for bounded or one-signed Borel $u$
-- statement:
--   Let $X = A\times S\times A\times S\times\cdots$ be the set of futures and $P(X)$ the set of probability measures on $X$, with the smallest σ-field $\Sigma^*$ for which $\nu\mapsto\nu(B)$ is measurable for every Borel $B\subseteq X$. Let $u$ be a Borel function on $S\times X$ that is bounded or of constant sign. Then
--   $$(s,\nu)\ \longmapsto\ \nu u(s) = \int_X u(s,x)\,d\nu(x)$$
--   is measurable on $S\times P(X)$.
--
--   Applied to the total return $u(s,x) = \sum_n r(s_n,a_n,s_{n+1})$, it makes $(s,\nu)\mapsto$ (expected return under $\nu$) measurable, which is how the optimal return becomes the projection of a Borel set in the proof of Theorem 7.1.
--
--   **Formalization Note** Three cases are stated: $u$ real, Borel and bounded (Bochner integral); $u$ extended-real, Borel and $\ge 0$ (the lower Lebesgue integral of $u$ as a value in $[0,\infty]$); $u$ extended-real, Borel and $\le 0$ (minus the lower Lebesgue integral of $-u$, a value in $[-\infty,0]$). $P(X)$ is the subtype of probability measures in Mathlib's `Measure X` with the Giry σ-field, which is $\Sigma^*$. $X$ is `ℕ → A × S` with the product σ-field.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 884, Lemma 7.1

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
import Definitions.Def_NegativeDP_OptEq_Futures
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Lemma 7.1, p. 884: if `u` is a Baire function on `SX` that is bounded or of
constant sign, then `(s, ν) ↦ νu(s) = ∫ u(s, x) dν(x)` is measurable on `S × P(X)`, where `X` is
the set of futures and `P(X)` the probability measures on `X` with the Giry σ-field. -/
theorem lemma71 :
    (∀ u : S × Futures S A → ℝ, Measurable u → (∃ C : ℝ, ∀ x, |u x| ≤ C) →
      Measurable (fun p : S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν} =>
        ∫ x, u (p.1, x) ∂(p.2 : Measure (Futures S A)))) ∧
    (∀ u : S × Futures S A → EReal, Measurable u → (∀ x, 0 ≤ u x) →
      Measurable (fun p : S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν} =>
        ∫⁻ x, (u (p.1, x)).toENNReal ∂(p.2 : Measure (Futures S A)))) ∧
    (∀ u : S × Futures S A → EReal, Measurable u → (∀ x, u x ≤ 0) →
      Measurable (fun p : S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν} =>
        -(((∫⁻ x, (-(u (p.1, x))).toENNReal ∂(p.2 : Measure (Futures S A))) : ℝ≥0∞) :
          EReal))) := by sorry

end NegativeDP.OptEq
