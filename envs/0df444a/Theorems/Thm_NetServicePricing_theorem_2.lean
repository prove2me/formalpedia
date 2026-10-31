-- Prove2me | Theorems.Thm_NetServicePricing_theorem_2
-- name    : NetServicePricing.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:14.732988+00:00
-- url     : https://prove2.me/theorems/2f0e5fee-f40f-4c7f-ba6e-20d1f78a0b83
-- title:
--   Theorem 2 — balanced networks share one optimal policy and revenue, the lowest among all networks with the same $n$ and average degree
-- statement:
--   Fix the number of consumers $n$, an average degree $\mathcal D$, the habit coefficient $\mu\in[0,1]$, the discount factor $\delta\in(0,1)$ and $\alpha,\beta>0$. Consider the class of all networks with $n$ consumers and average degree $\mathcal D$ that satisfy Assumption 1 (imposed throughout the paper). Revenues are those of policies $(\tau,p)$ with one price adjustment, from zero initial consumption.
--
--   1. **All balanced networks are equivalent.** If $B_1$ and $B_2$ are balanced networks of the class, then every policy $\pi$ earns the same revenue on both, $J_{B_1}(\mathbf 0;\pi)=J_{B_2}(\mathbf 0;\pi)$; hence their optimal revenues coincide, and a policy is optimal for $B_1$ if and only if it is optimal for $B_2$.
--   2. **Balanced networks are the worst.** If $B$ is a balanced network of the class and $M$ is any network of the class, then every policy earns at most as much on $B$ as on $M$, $J_B(\mathbf 0;\pi)\le J_M(\mathbf 0;\pi)$; hence the optimal revenue of $B$ is at most that of $M$:
--
--   $$J_B(\mathbf 0)=\max_{\pi\in\Pi}J_B(\mathbf 0;\pi)\ \le\ \max_{\pi\in\Pi}J_M(\mathbf 0;\pi)=J_M(\mathbf 0).$$
--
--   Holding the average degree fixed, the heterogeneity of the weighted degrees can only help the firm, and the firm needs no structural information about a network beyond its being balanced and its average degree.
--
--   Differences from the source:
--   - generalization: (i) optimal policy and revenue are the same; (ii) balanced networks generate the lowest revenue → in addition, the revenue of every single policy is equal across balanced networks and lowest on balanced networks; reason: the paper's proof (EC.3.2) establishes the per-policy statements, which imply the printed clauses, also stated
--   - reading: the optimal pricing policy is the same for all balanced networks → a policy is optimal for B₁ if and only if it is optimal for B₂; reason: the optimal policy need not be unique, so "the same" is read as equality of the sets of optimal policies
--   - reading: policies (τ, p) with a price p → τ ∈ ℕ and p ∈ [0, α/β]; reason: (2) is valid "provided that x*i,t > 0" and (4) is written "for any fixed price p ≤ α/β"; prices are nonnegative
--   - reading: α, β constant coefficients → 0 < α, 0 < β; reason: the quadratic term of (1) has the negative sign to induce concavity, which needs β > 0, and the price cap α/β with nonnegative prices needs α ≥ 0; standing assumption of every statement
--   - encoding: Assumption 1 on the ordered eigenvalues: −1 − λₙ < μ < 1 − λ₁ and δ ≥ 2 − 1/(λ₁ + μ) → for every eigenvalue λ of M: −1 < λ + μ < 1 and (2 − δ)(λ + μ) ≤ 1; reason: equivalent for λ₁ + μ > 0; at λ₁ + μ = 0 (M = 0, μ = 0) the printed 1/0 is undefined and read as satisfied
--   - encoding: max over policies of the series (3) → a real tsum per policy and a real supremum over the policy class; reason: under Assumption 1 the series converge absolutely and the revenues are bounded, so both are genuine
--   - encoding: periods t = 1, 2, … and consumers 1, …, n → the sum over t ∈ ℕ of the term for period t + 1, and consumers Fin n; reason: reindexing only
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Theorem 2, p.20

import Mathlib
import Definitions.Def_NetServicePricing_InClass
import Definitions.Def_NetServicePricing_IsBalanced
import Definitions.Def_NetServicePricing_Policy
import Definitions.Def_NetServicePricing_revenue
import Definitions.Def_NetServicePricing_optimalRevenue
import Definitions.Def_NetServicePricing_IsOptimal

open Matrix

namespace NetServicePricing

/-- **Theorem 2 (balanced networks share one optimal policy and revenue, the lowest of their
class).**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Theorem 2, p.20: "Consider the class of all networks with n consumers and average degree
D. (i) The firm's optimal pricing policy and revenue is the same for all balanced networks in
this class. (ii) Among all networks in this class, balanced networks generate the lowest possible
revenue for the firm."

The class (`InClass D μ δ`) consists of the networks on `Fin n` with average degree `D` that
satisfy Assumption 1, which the paper imposes throughout; `μ ∈ [0,1]`, `δ ∈ (0,1)`, `α, β > 0`.
(i) Any two balanced networks of the class give every policy the same revenue, have the same
optimal revenue and the same optimal policies. (ii) Every balanced network of the class gives
every policy at most the revenue that any network of the class gives it, and has at most its
optimal revenue.

**Formalization Note** Policies are `(τ, p)` with `τ ∈ ℕ`, `p ∈ [0, α/β]`; revenue is the real
`tsum` of (3) from `x₀ = 0`, the optimal revenue its real supremum over policies. The per-policy
clauses are stronger than the printed statement and imply its other clauses. -/
theorem theorem_2 (n : ℕ) (D μ δ α β : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hα : 0 < α) (hβ : 0 < β) :
    (∀ B₁ B₂ : Matrix (Fin n) (Fin n) ℝ, InClass D μ δ B₁ → InClass D μ δ B₂ →
        IsBalanced B₁ → IsBalanced B₂ →
        (∀ π : Policy α β, revenue B₁ μ α β δ π.1 π.2 = revenue B₂ μ α β δ π.1 π.2) ∧
        optimalRevenue B₁ μ α β δ = optimalRevenue B₂ μ α β δ ∧
        (∀ π : Policy α β, IsOptimal B₁ μ α β δ π ↔ IsOptimal B₂ μ α β δ π)) ∧
    (∀ M B : Matrix (Fin n) (Fin n) ℝ, InClass D μ δ M → InClass D μ δ B → IsBalanced B →
        (∀ π : Policy α β, revenue B μ α β δ π.1 π.2 ≤ revenue M μ α β δ π.1 π.2) ∧
        optimalRevenue B μ α β δ ≤ optimalRevenue M μ α β δ) := by sorry

end NetServicePricing
