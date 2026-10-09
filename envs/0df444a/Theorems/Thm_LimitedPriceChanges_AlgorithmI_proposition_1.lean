-- Prove2me | Theorems.Thm_LimitedPriceChanges_AlgorithmI_proposition_1
-- name    : LimitedPriceChanges.AlgorithmI.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:27.360718+00:00
-- url     : https://prove2.me/theorems/7009d6fa-ad9f-42dc-81e9-f7c026260dbc
-- title:
--   Proposition 1, p. 10 — the censored MLE ẑᵢ satisfies ℙ{|z − ẑᵢ| ≥ ϵ} ≤ K₃e^{−K₄Iᵢϵ²} + K₅/Iᵢ
-- statement:
--   Consider the censored pricing-inventory model with a scalar parameter under the standing hypotheses of §2–§3 at the true parameter $z$ (Assumption A, optimal levels above $d^l$, Definition 1 and Assumption 1), and run Algorithm-I with valid inputs $m\ge1$, $\hat p_1\in\mathcal P$, $\hat y_1\in\mathcal Y$, $\Delta\ge1$ and any maximum-likelihood and plug-in selections. Let $\hat z_i$ be the censored-data maximum-likelihood estimate (5) computed from the $I_i$ periods of stage $i$.
--
--   There are constants $K_3,K_4,K_5>0$ such that, for every large enough horizon $T$, every stage $i\in\{1,\dots,m+1\}$ and every $\epsilon>0$,
--   $$
--   \mathbb P\{|z-\hat z_i|\ge\epsilon\}\le K_3e^{-K_4I_i\epsilon^2}+\frac{K_5}{I_i}. \tag{7}
--   $$
--
--   This is a large-deviation bound for maximum likelihood from censored, dependent and non-identically distributed sales data; it is the estimation input to the regret analysis of Algorithm-I.
--
--   **Formalization Note** The printed "for any $\epsilon>0$ and large enough $i$" cannot mean large $i$, since $i\le m+1$ with $m$ fixed; the proof's thresholds are on $T$ (through $I_1=\lceil T^{1/(m+1)}\rceil$), and Theorem B1 needs constants uniform in $\epsilon$. The statement reads it as: for $T$ large enough, uniformly in $i$ and $\epsilon$. The probability is the sum of the path weights $\prod_t f(d_t;p_t,z)$ over the demand paths in the event, compared in $[0,\infty]$. $I_i$ is the stage length of Step 0 at horizon $T$.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 10, Proposition 1, (7); proof pp. 27–35

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm

namespace LimitedPriceChanges.AlgorithmI

/-- **Proposition 1** (p. 10). There are constants `K₃, K₄, K₅ > 0` such that, for `T` large
enough, every stage `i ∈ {1, …, m + 1}` and every `ϵ > 0`, the censored-data MLE `ẑᵢ` of (5)
satisfies `ℙ{|z − ẑᵢ| ≥ ϵ} ≤ K₃ e^{−K₄ Iᵢ ϵ²} + K₅ / Iᵢ` (7). The printed "large enough `i`" is
read as "`T` large enough, uniformly in `i` and `ϵ`". -/
theorem proposition_1 (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z)
    (hA : A.Valid) :
    ∃ K₃ K₄ K₅ : ℝ, 0 < K₃ ∧ 0 < K₄ ∧ 0 < K₅ ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      ∀ i ∈ Finset.Icc 1 (A.m + 1), ∀ ϵ : ℝ, 0 < ϵ →
        A.prob z T {d | ϵ ≤ |z - A.zhat T i d|} ≤
          ENNReal.ofReal (K₃ * Real.exp (-(K₄ * (A.stageLen T i : ℝ) * ϵ ^ 2)) +
            K₅ / (A.stageLen T i : ℝ)) := by sorry

end LimitedPriceChanges.AlgorithmI
