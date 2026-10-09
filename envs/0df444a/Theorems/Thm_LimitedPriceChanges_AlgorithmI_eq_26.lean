-- Prove2me | Theorems.Thm_LimitedPriceChanges_AlgorithmI_eq_26
-- name    : LimitedPriceChanges.AlgorithmI.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:38.581988+00:00
-- url     : https://prove2.me/theorems/6443ce25-7423-4f35-baad-ea0446d604f5
-- title:
--   (26), p. 25 — the inventory exploration of stage i ≥ 2 is triggered with probability ℙ(ŷᵢ ≠ ỹᵢ) ≤ K/Iᵢ₋₁
-- statement:
--   Consider the censored pricing-inventory model with a scalar parameter under the standing hypotheses of §2–§3 at the true parameter $z$, and run Algorithm-I with valid inputs. In stage $i$, Step 1 replaces the computed target $\hat y_i$ by $\tilde y_i\ne\hat y_i$ only when $\hat y_i=d^l$ (inventory exploration).
--
--   There is a constant $K>0$ such that, for every large enough horizon $T$ and every stage $i\in\{2,\dots,m+1\}$,
--   $$
--   \mathbb P(\hat y_i\ne\tilde y_i)\le\frac{K}{I_{i-1}} . \tag{26}
--   $$
--
--   Since every optimal order-up-to level exceeds $d^l$, exploration happens only when the previous estimate is far from $z$; this bounds the third part of the regret decomposition (23).
--
--   **Formalization Note** The page writes the constant as $K_3+K_5$, built from the existential constants of Proposition 1; here it is an existential $K>0$. The page's intermediate probabilities are written with $\hat z_i$; since $\hat y_i$ is computed from $\hat z_{i-1}$ they should read $\hat z_{i-1}$, and only the final bound, which concerns $\hat y_i$ and $\tilde y_i$, is stated. Probabilities are path-weighted sums in $[0,\infty]$.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 25, (26)

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm

namespace LimitedPriceChanges.AlgorithmI

/-- **(26)**, p. 25: the inventory exploration of Step 1 is rarely triggered after stage 1. There
is a constant `K > 0` (the paper's `K₃ + K₅`) such that, for `T` large enough and every stage
`i ∈ {2, …, m + 1}`, `ℙ(ŷᵢ ≠ ỹᵢ) ≤ K / Iᵢ₋₁`. (The printed middle terms use `ẑᵢ`; the target
`ŷᵢ` is computed from `ẑᵢ₋₁`.) -/
theorem eq_26 (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z) (hA : A.Valid) :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ i ∈ Finset.Icc 2 (A.m + 1),
      A.prob z T {d | A.yhat T i d ≠ A.ytilde T i d} ≤
        ENNReal.ofReal (K / (A.stageLen T (i - 1) : ℝ)) := by sorry

end LimitedPriceChanges.AlgorithmI
