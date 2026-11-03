-- Prove2me | Theorems.Thm_OnDemandCoord_platform_identity
-- name    : OnDemandCoord.platform_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:30.460328+00:00
-- url     : https://prove2.me/theorems/f5d7b37a-fd06-4c06-816e-4b9980f3eec9
-- title:
--   The platform's profit under the contract: $\Pi\le -C(Q,\eta)+p\sum(1-m_i)\mathbb E[\hat X_i]+c\sum Q_i+\sum r_i$, with equality when no-waste
-- statement:
--   **The platform's profit under the contract** (§5.2.1, pp. 19–20). Let $Q\ge0$, $\eta\in\mathbb R$, a contract with fees $r_i$, parameters $m_i$ and target fill rates $\beta_i>0$, and a policy $\kappa\in\mathcal A$. Then the platform's expected profit (2) satisfies
--   $$\Pi(\eta,\kappa\mid Q)\ \le\ -C(Q,\eta)+p\sum_{i\in I}(1-m_i)\,\mathbb E[(X_i-Q_i)^+]+c\sum_{i\in I}Q_i+\sum_{i\in I}r_i,$$
--   with equality when $\kappa$ satisfies the no-waste condition (4).
--
--   So, with $Q$ fixed, maximizing the platform's profit over $\eta$ is minimizing the system cost $C(Q,\cdot)$, and among policies in $\mathcal A$ the no-waste ones are optimal for the platform.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - generalization: the equality for a no-waste policy → also the inequality for every policy in 𝒜; reason: the paper's comparison of policies on p. 20 uses it; it specializes to the printed equality
--   - encoding: w_i^F and w_i^C divide by β*_i → hypothesis β_i > 0 for every i; reason: (11)–(12) are undefined at β_i = 0
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), §5.2.1, display on pp. 19–20

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **The platform identity**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), §5.2.1, pp. 19–20. For `Q ≥ 0`, positive target fill rates
and any `m`, `r`, every policy in `𝒜` has
`Π(η, κ | Q) ≤ −C(Q, η) + p ∑_i (1 − m_i) E[(X_i − Q_i)⁺] + c ∑_i Q_i + ∑_i r_i`, with equality
when the policy is no-waste. The equality is the last display of p. 20. -/
theorem platform_identity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Q : Fin n → ℝ) (hQ : 0 ≤ Q) (η : ℝ) (K : Contract n) (hβ : ∀ i, 0 < K.β i)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (hκ : IsPolicy κ) :
    M.platformProfit K η κ Q ≤
        -M.C Q η + M.p * ∑ i, (1 - K.m i) * M.mean Q i + M.c * ∑ i, Q i + ∑ i, K.r i ∧
      (IsNoWaste κ → M.platformProfit K η κ Q =
        -M.C Q η + M.p * ∑ i, (1 - K.m i) * M.mean Q i + M.c * ∑ i, Q i + ∑ i, K.r i) := by sorry

end OnDemandCoord
