-- Prove2me | Theorems.Thm_LearningBasedRO_lemma_3
-- name    : LearningBasedRO.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:03.804856+00:00
-- url     : https://prove2.me/theorems/0f8fe496-7436-4fc9-bdda-308e95d7c925
-- title:
--   Lemma 3 — order-statistic confidence bounds for the $(1-\epsilon)$-quantile
-- statement:
--   Let $Y_1,\dots,Y_{n_2}$ be i.i.d. real data from a continuous (atomless) distribution with distribution function $F$, let $Y_{(1)}\le\dots\le Y_{(n_2)}$ be the order statistics, let $0<\epsilon<1$, $0<\delta<1$, and let $q_{1-\epsilon}$ be a $(1-\epsilon)$-quantile, $F(q_{1-\epsilon})=1-\epsilon$. Write $b_k=\binom{n_2}{k}(1-\epsilon)^k\epsilon^{n_2-k}$.
--
--   1. If $i^*=\min\{r:\sum_{k=0}^{r-1}b_k\ge 1-\delta,\ 1\le r\le n_2\}$ exists, then $Y_{(i^*)}$ is a $1-\delta$ confidence upper bound for $q_{1-\epsilon}$:
--   $$P\big(Y_{(i^*)}\ge q_{1-\epsilon}\big)\ge 1-\delta .$$
--   2. $\sum_{k=0}^{n_2-1}b_k=1-(1-\epsilon)^{n_2}$, and if this is $<1-\delta$, then no $Y_{(r)}$, $1\le r\le n_2$, is a valid confidence upper bound: $P(Y_{(r)}\ge q_{1-\epsilon})<1-\delta$.
--   3. If $i_*=\max\{r:\sum_{k=r}^{n_2}b_k\ge 1-\delta,\ 1\le r\le n_2\}$ exists, then $Y_{(i_*)}$ is a $1-\delta$ confidence lower bound:
--   $$P\big(Y_{(i_*)}\le q_{1-\epsilon}\big)\ge 1-\delta .$$
--   4. $\sum_{k=1}^{n_2}b_k=1-\epsilon^{n_2}$, and if this is $<1-\delta$, then no $Y_{(r)}$, $1\le r\le n_2$, is a valid confidence lower bound: $P(Y_{(r)}\le q_{1-\epsilon})<1-\delta$.
--
--   The upper bound is what calibrates the size of the learned uncertainty set in Phase 2 of the procedure; Theorem 1 applies it conditionally on the Phase 1 data.
--
--   Differences from the source:
--   - reading: data from a continuous distribution → the law μ is atomless (NullSingletonClass μ); reason: the weakest standard meaning of a continuous distribution
--   - reading: ϵ, δ levels (range not stated) → 0 < ϵ < 1, 0 < δ < 1; reason: the meaningful range, used throughout the paper
--   - generalization: the (1 − ϵ)-quantile → every real q with F(q) = 1 − ϵ; reason: for an atomless law every (1 − ϵ)-quantile satisfies this, so every quantile convention is covered
--   - encoding: "Y(r) is a valid 1 − δ confidence upper (lower) bound", "none of the Y(r)'s is valid", "i∗ exists", "or equivalently" → P^{n₂}(q ≤ Y(r)) ≥ 1 − δ (P^{n₂}(Y(r) ≤ q) ≥ 1 − δ), the probability is < 1 − δ for every 1 ≤ r ≤ n₂, the defining set is nonempty, the identity of the two sums as a separate conjunct; reason: the meanings the proof of Lemma 3 uses (p.8), same instances
--   - encoding: strictly ordered order statistics Y(1) < ⋯ < Y(n₂) → order statistics counted with multiplicity, ranks 1-based; reason: ties have probability 0 for an atomless law
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, Lemma 3, p.8 (proof pp.8–9)

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

/-- **Lemma 3.** Let `Y₁, …, Y_{n₂}` be i.i.d. data in `ℝ` from a continuous distribution `μ`,
`Y₍₁₎ ≤ ⋯ ≤ Y₍ₙ₂₎` the order statistics, and `q` the `(1 - ϵ)`-quantile.
1. If `i*` of (4) exists, `Y₍ᵢ*₎` is a `1 - δ` confidence upper bound for `q`:
   `P(Y₍ᵢ*₎ ≥ q) ≥ 1 - δ`.
2. `Σ_{k=0}^{n₂-1} C(n₂,k)(1-ϵ)^k ϵ^(n₂-k) = 1 - (1-ϵ)^{n₂}`, and if this is `< 1 - δ` then no
   `Y₍ᵣ₎` (`1 ≤ r ≤ n₂`) is a valid `1 - δ` confidence upper bound.
3. If `i_*` exists, `Y₍ᵢ_*₎` is a `1 - δ` confidence lower bound: `P(Y₍ᵢ_*₎ ≤ q) ≥ 1 - δ`.
4. `Σ_{k=1}^{n₂} C(n₂,k)(1-ϵ)^k ϵ^(n₂-k) = 1 - ϵ^{n₂}`, and if this is `< 1 - δ` then no `Y₍ᵣ₎`
   is a valid `1 - δ` confidence lower bound.
Hong–Huang–Lam, arXiv:1704.04342v2, Lemma 3, p.8 (proof pp.8–9).

**Formalization Note** "Continuous" is read as atomless (`NullSingletonClass μ`); `q` is any real
with `F(q) = μ(-∞, q] = 1 - ϵ` (every `(1 - ϵ)`-quantile); `0 < ϵ < 1`, `0 < δ < 1`. "`i*` exists"
is the nonemptiness of the set of (4) (`iStarSet`), likewise for `i_*` (`iLowerStarSet`); when
nonempty, `iStar`/`iLowerStar` are its minimum/maximum. Order statistics are counted with
multiplicity and ranks are 1-based. -/
theorem lemma_3 (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] (n₂ : ℕ)
    (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (q : ℝ)
    (hq : μ (Set.Iic q) = ENNReal.ofReal (1 - ϵ)) :
    ((iStarSet n₂ ϵ δ).Nonempty →
        ENNReal.ofReal (1 - δ) ≤
          (Measure.pi fun _ : Fin n₂ => μ) {y | q ≤ orderStat y (iStar n₂ ϵ δ)}) ∧
      ((∑ k ∈ Finset.range n₂, binomTerm n₂ ϵ k = 1 - (1 - ϵ) ^ n₂) ∧
        (∑ k ∈ Finset.range n₂, binomTerm n₂ ϵ k < 1 - δ →
          ∀ r : ℕ, 1 ≤ r → r ≤ n₂ →
            (Measure.pi fun _ : Fin n₂ => μ) {y | q ≤ orderStat y r} <
              ENNReal.ofReal (1 - δ))) ∧
      ((iLowerStarSet n₂ ϵ δ).Nonempty →
        ENNReal.ofReal (1 - δ) ≤
          (Measure.pi fun _ : Fin n₂ => μ) {y | orderStat y (iLowerStar n₂ ϵ δ) ≤ q}) ∧
      ((∑ k ∈ Finset.Icc 1 n₂, binomTerm n₂ ϵ k = 1 - ϵ ^ n₂) ∧
        (∑ k ∈ Finset.Icc 1 n₂, binomTerm n₂ ϵ k < 1 - δ →
          ∀ r : ℕ, 1 ≤ r → r ≤ n₂ →
            (Measure.pi fun _ : Fin n₂ => μ) {y | orderStat y r ≤ q} <
              ENNReal.ofReal (1 - δ))) := by sorry

end LearningBasedRO
