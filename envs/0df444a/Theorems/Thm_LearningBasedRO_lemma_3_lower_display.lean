-- Prove2me | Theorems.Thm_LearningBasedRO_lemma_3_lower_display
-- name    : LearningBasedRO.lemma_3_lower_display
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:30:53.692027+00:00
-- url     : https://prove2.me/theorems/43d48c33-0b54-4b31-a7c4-f911dfae1cc3
-- title:
--   Proof of Lemma 3, second display — $P(Y_{(r)}\le q_{1-\epsilon})=\sum_{k=r}^{n}\binom{n}{k}(1-\epsilon)^k\epsilon^{n-k}$
-- statement:
--   Let $Y_1,\dots,Y_n$ be i.i.d. real random variables with an atomless law $\mu$ and distribution function $F$, let $0<\epsilon<1$, and let $q_{1-\epsilon}$ be a $(1-\epsilon)$-quantile, $F(q_{1-\epsilon})=1-\epsilon$. Let $Y_{(1)}\le\dots\le Y_{(n)}$ be the order statistics. For every $1\le r\le n$:
--
--   1. $Y_{(r)}\le q_{1-\epsilon}$ if and only if at least $r$ of $Y_1,\dots,Y_n$ are $\le q_{1-\epsilon}$;
--   2. $$P\big(Y_{(r)}\le q_{1-\epsilon}\big)=\sum_{k=r}^{n}\binom{n}{k}(1-\epsilon)^k\epsilon^{\,n-k}.$$
--
--   This is the binomial computation behind the lower confidence bound of Lemma 3.
--
--   Differences from the source:
--   - reading: data from a continuous distribution → μ atomless (NullSingletonClass μ); reason: the weakest standard meaning of a continuous distribution
--   - reading: ϵ a tolerance level (range not stated) → 0 < ϵ < 1; reason: the meaningful range, used throughout the paper
--   - generalization: the (1 − ϵ)-quantile q₁₋ϵ → every real q with F(q) = 1 − ϵ; reason: for an atomless law every (1 − ϵ)-quantile satisfies this, so every quantile convention is covered
--   - encoding: sample size n₂ and the middle line Σ C(n₂,k)F(q)^k F̄(q)^{n₂−k} → n, the event identity and the final value (the middle line equals the last since F(q) = 1 − ϵ is a hypothesis); ranks 1 ≤ r ≤ n; order statistics with multiplicity; reason: Lean conventions, same instances (ties have probability 0)
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, proof of Lemma 3, second display, pp.8–9

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

/-- **Proof of Lemma 3, second display.** Let `Y₁, …, Yₙ` be i.i.d. with an atomless law `μ` on
`ℝ`, and let `q` be a `(1 - ϵ)`-quantile, `F(q) = 1 - ϵ`. For `1 ≤ r ≤ n`,
`Y₍ᵣ₎ ≤ q` exactly when at least `r` of the data are `≤ q`, and
`P(Y₍ᵣ₎ ≤ q) = Σ_{k=r}^{n} C(n,k) (1 - ϵ)^k ϵ^(n-k)`.
Hong–Huang–Lam, arXiv:1704.04342v2, proof of Lemma 3, second display, pp.8–9.

**Formalization Note** The sample size `n` is the page's `n₂`. "Continuous distribution" is read
as atomless (`NullSingletonClass μ`). `q` is any real with `F(q) = μ(-∞, q] = 1 - ϵ`. The rank
`r` is 1-based; order statistics are counted with multiplicity (`orderStat`). -/
theorem lemma_3_lower_display (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (q : ℝ) (hq : μ (Set.Iic q) = ENNReal.ofReal (1 - ϵ))
    (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    {y : Fin n → ℝ | orderStat y r ≤ q} =
        {y : Fin n → ℝ | r ≤ (Finset.univ.filter (fun j => y j ≤ q)).card} ∧
      (Measure.pi fun _ : Fin n => μ) {y | orderStat y r ≤ q} =
        ENNReal.ofReal (∑ k ∈ Finset.Icc r n, binomTerm n ϵ k) := by sorry

end LearningBasedRO
