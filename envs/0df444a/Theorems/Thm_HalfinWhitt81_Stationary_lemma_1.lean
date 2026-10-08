-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_lemma_1
-- name    : HalfinWhitt81.Stationary.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:47:06.279869+00:00
-- url     : https://prove2.me/theorems/c552a0ee-2976-44e2-9564-6771e2ac42ae
-- title:
--   Lemma 1 — recursions for the partial moments σ₁^{(m)}, σ₂^{(m)} of the M/M/s stationary queue length
-- statement:
--   Consider a single M/M/s queue with $s \ge 1$ servers, arrival rate $\lambda > 0$, service rate $\mu > 0$ and traffic intensity $\rho = \lambda/(s\mu) < 1$. Let $p_k = P(Q(\infty) = k)$, $k = 0,1,2,\dots$, be its stationary distribution: a probability distribution solving the balance equations of the birth–death process with birth rate $\lambda$ and death rate $\min(k,s)\mu$ in state $k$. Write $\alpha = P(Q(\infty) \ge s)$ for the probability of delay (1.2), and split the moments of $Q(\infty)$ as in (1.4):
--   $$\sigma_1^{(m)} = \sum_{k=0}^{s-1} k^m p_k, \qquad \sigma_2^{(m)} = \sum_{k=s}^{\infty} k^m p_k, \qquad m = 0,1,2,\dots$$
--
--   Then every series $\sigma_2^{(m)}$ converges, and for every $m \ge 1$
--   $$\sigma_1^{(m)} = \rho s \sum_{i=0}^{m-1} \binom{m-1}{i} \sigma_1^{(i)} - s^m \alpha (1-\rho), \qquad \sigma_2^{(m)} = \rho (1-\rho)^{-1} \sum_{i=0}^{m-1} \binom{m}{i} \sigma_2^{(i)} + s^m \alpha .$$
--
--   Starting from $\sigma_1^{(0)} = 1-\alpha$ and $\sigma_2^{(0)} = \alpha$, the two recursions give all moments $E\,Q(\infty)^m = \sigma_1^{(m)} + \sigma_2^{(m)}$ in terms of $\alpha$; the paper uses them for the mean and variance (1.8), the moments about $s$ (1.9) and the uniform bound behind Corollary 1.
--
--   **Formalization Note** The paper writes "$m = 0, 1, \cdots$" for the definitions (1.4); the recursions themselves are asserted for $m \ge 1$, the only range in which they hold (at $m = 0$ the right-hand sides are empty sums minus or plus $\alpha$). The convergence of $\sigma_2^{(m)}$, implicit in the paper, is part of the conclusion. Lean's convention $0^0 = 1$ makes $\sigma_1^{(0)} = \sum_{k<s} p_k$, as in the paper. The stationary distribution is the `IsSteadyState` predicate of the referenced definition `QueueingFundamentals.BirthDeath.Balance`, with death rates `mmcDeath μ s`.
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 572, Lemma 1 (with (1.4), p. 571)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_HalfinWhitt81_Stationary_Basic

namespace HalfinWhitt81.Stationary

open QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Lemma 1, p. 572, with the partial moments (1.4), p. 571. For one `M/M/s`
queue (`s ≥ 1` servers, arrival rate `λ > 0`, service rate `μ > 0`, `ρ = λ/(sμ) < 1`) with
stationary law `p`, let `α = P(Q(∞) ≥ s)`, `σ₁^{(m)} = ∑_{k=0}^{s−1} k^m p_k` and
`σ₂^{(m)} = ∑_{k≥s} k^m p_k`. Then every series `σ₂^{(m)}` converges, and for every `m ≥ 1`
`σ₁^{(m)} = ρs ∑_{i=0}^{m−1} C(m−1, i) σ₁^{(i)} − s^m α (1 − ρ)` and
`σ₂^{(m)} = ρ(1 − ρ)⁻¹ ∑_{i=0}^{m−1} C(m, i) σ₂^{(i)} + s^m α`. -/
theorem lemma_1 (lam μ : ℝ) (s : ℕ) (ρ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hs : 1 ≤ s)
    (hρ : ρ = lam / (s * μ)) (hρ1 : ρ < 1) (p : ℕ → ℝ)
    (hp : IsSteadyState (fun _ => lam) (mmcDeath μ s) p) :
    let α : ℝ := probGE p s
    let σ₁ : ℕ → ℝ := fun m => ∑ k ∈ Finset.range s, (k : ℝ) ^ m * p k
    let σ₂ : ℕ → ℝ := fun m => ∑' k : ℕ, if s ≤ k then (k : ℝ) ^ m * p k else 0
    (∀ m : ℕ, Summable (fun k : ℕ => if s ≤ k then (k : ℝ) ^ m * p k else 0)) ∧
      ∀ m : ℕ, 1 ≤ m →
        σ₁ m = ρ * s * (∑ i ∈ Finset.range m, ((m - 1).choose i : ℝ) * σ₁ i)
            - (s : ℝ) ^ m * α * (1 - ρ) ∧
          σ₂ m = ρ * (1 - ρ)⁻¹ * (∑ i ∈ Finset.range m, (m.choose i : ℝ) * σ₂ i)
            + (s : ℝ) ^ m * α := by sorry

end HalfinWhitt81.Stationary
