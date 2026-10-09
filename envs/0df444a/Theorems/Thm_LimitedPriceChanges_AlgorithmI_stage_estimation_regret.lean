-- Prove2me | Theorems.Thm_LimitedPriceChanges_AlgorithmI_stage_estimation_regret
-- name    : LimitedPriceChanges.AlgorithmI.stage_estimation_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:27.255667+00:00
-- url     : https://prove2.me/theorems/4660d2fb-3a68-483b-ad7d-fd6130a83e5d
-- title:
--   p. 25, before (25) — the plug-in decision of stage i satisfies 𝔼[G*(z) − G(p̂ᵢ, ŷᵢ, z)] ≤ K₁₇/Iᵢ₋₁
-- statement:
--   Consider the censored pricing-inventory model with a scalar parameter under the standing hypotheses of §2–§3 at the true parameter $z$, and run Algorithm-I with valid inputs. For a stage $i\ge2$, the decision $(\hat p_i,\hat y_i)$ is computed by (6) from the estimate $\hat z_{i-1}$ of the previous stage, which used $I_{i-1}$ periods of data.
--
--   There is a constant $K_{17}>0$ such that, for every large enough horizon $T$ and every stage $i\in\{2,\dots,m+1\}$,
--   $$
--   \mathbb E\big[G^*(z)-G(\hat p_i,\hat y_i,z)\big]\le\frac{K_{17}}{I_{i-1}} .
--   $$
--
--   The paper obtains this by combining Proposition 1 with Theorem B1; summed over the periods of the stages it gives the estimation-error part of the regret decomposition (23).
--
--   **Formalization Note** $\hat p_i=p^*_{\hat y_i}(\hat z_{i-1})$ with $\hat y_i$ the order-up-to selection at $\hat z_{i-1}$. The expectation is the path-weighted sum in $[0,\infty]$ of the nonnegative gap. "For large $T$" is an explicit threshold $T_0$, uniform in $i$.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 25, display before (25)

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm

namespace LimitedPriceChanges.AlgorithmI

/-- **p. 25, before (25)** ("by combining Proposition 1 and Theorem B1"). There is a constant
`K₁₇ > 0` such that, for `T` large enough and every stage `i ∈ {2, …, m + 1}`, the plug-in
decision `(p̂ᵢ, ŷᵢ)` computed by (6) from `ẑᵢ₋₁` satisfies
`𝔼[G*(z) − G(p̂ᵢ, ŷᵢ, z)] ≤ K₁₇ / Iᵢ₋₁`. -/
theorem stage_estimation_regret (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z)
    (hA : A.Valid) :
    ∃ K₁₇ : ℝ, 0 < K₁₇ ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ i ∈ Finset.Icc 2 (A.m + 1),
      A.expect z T (fun d =>
          ENNReal.ofReal (S.Gstar A.pstar z - S.G (A.phat T i d) (A.yhat T i d) z)) ≤
        ENNReal.ofReal (K₁₇ / (A.stageLen T (i - 1) : ℝ)) := by sorry

end LimitedPriceChanges.AlgorithmI
