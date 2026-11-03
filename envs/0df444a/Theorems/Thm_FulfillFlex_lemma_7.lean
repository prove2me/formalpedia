-- Prove2me | Theorems.Thm_FulfillFlex_lemma_7
-- name    : FulfillFlex.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:24:29.956207+00:00
-- url     : https://prove2.me/theorems/2464addc-2214-4298-854b-53d127044877
-- title:
--   Lemma 7, p.49 — $\mathbb E[(\sum_{i\le T}X_i-T\mu)^+]\le\frac12\sqrt T\sigma$ for i.i.d. $X_i$
-- statement:
--   Let $X_1,\dots,X_T$ be i.i.d. real random variables with finite mean $\mu$ and finite variance $\sigma^2$. Then
--
--   $$
--   \mathbb E\Bigl[\Bigl(\sum_{1\le i\le T}X_i-T\mu\Bigr)^+\Bigr]\le\frac12\sqrt T\,\sigma.
--   $$
--
--   This bound on the expected positive deviation is the source of the $\sqrt T$ rate of Proposition 3: it is applied to total demand at each DC and to the abandonment coins.
--
--   **Formalization Note** The sequence is indexed from $0$ and the sum runs over `Finset.range T`. The conclusion also states that the positive part is integrable.
--
--   Differences from the source:
--   - encoding: X_1, …, X_T, T a positive integer → the first T terms of an i.i.d. sequence X 0, X 1, …, every T : ℕ; reason: reindexing; at T = 0 both sides are 0
--   - encoding: E[(·)⁺] is a number → the conclusion states integrability together with the bound on the Bochner integral; reason: a Bochner integral of a non-integrable function would be 0
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Lemma 7, p.49

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FulfillFlex

/-- **Lemma 7 (expected positive deviation of an i.i.d. sum).**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Lemma 7, p.49: for `T` i.i.d. random
variables with finite mean `μ` and finite variance `σ²`,
`E[(∑_{1≤i≤T} X_i - Tμ)⁺] ≤ ½ √T σ`.

**Formalization Note** The first `T` terms `X 0, X 1, …` of the sequence are the paper's `X_1, …, X_T`. `MemLp (X 0) 2 P` is
"finite variance". The conclusion also records that the positive part is integrable, since a
Bochner integral of a non-integrable function is `0`. -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (X 0) 2 P) (T : ℕ) :
    Integrable (fun ω => max (∑ i ∈ Finset.range T, X i ω - T * ∫ ω', X 0 ω' ∂P) 0) P ∧
      ∫ ω, max (∑ i ∈ Finset.range T, X i ω - T * ∫ ω', X 0 ω' ∂P) 0 ∂P
        ≤ 1 / 2 * √(T : ℝ) * √(Var[X 0; P]) := by sorry

end FulfillFlex
