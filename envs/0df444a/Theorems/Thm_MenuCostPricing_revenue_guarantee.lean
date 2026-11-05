-- Prove2me | Theorems.Thm_MenuCostPricing_revenue_guarantee
-- name    : MenuCostPricing.revenue_guarantee
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:27.163822+00:00
-- url     : https://prove2.me/theorems/6f58af6c-5f91-4757-8ffd-591758bbf8c7
-- title:
--   §3.7 "The final revenue guarantee" — $R(\hat x)\ge(1-\epsilon)\cdot R(x^*)$
-- statement:
--   Fix an instance and $\epsilon>0$; let $\epsilon_h=\min(\epsilon,1)$ and $\delta=\epsilon_h/(8\varrho_{\max})$.
--   1. For every guess $(\Gamma,\hat w,\rho_{\mathrm{single}})$ with $\Gamma\subseteq[2,T]$, $\hat w\ge0$, $\rho_{\mathrm{single}}\ge0$, the strategy $\hat x$ the program derives satisfies $R(\hat x)\ge(1-3\delta\varrho_{\max})\cdot\hat{\mathcal R}_{2\delta,\delta}(\hat x)$.
--   2. For every budget-feasible $x$, at the guess $(\Gamma(x),\hat w,\max_i\hat{\mathcal R}^i_{2\delta,\delta}(x_i))$ with $w_t(x)\le\hat w_t\le(1+\delta)w_t(x)$, the program derives a strategy $\hat x$ with
--   $$
--   R(\hat x)\ge(1-\epsilon_h)\cdot R(x).
--   $$
--
--   For $\epsilon\le1$ and $x=x^*$ this is the chain $R(\hat x)\ge(1-3\delta\varrho_{\max})(1-2\delta)(1-3\delta)R(x^*)\ge(1-\epsilon)R(x^*)$ of §3.7.
--
--   Differences from the source:
--   - generalization: the optimal strategy x∗ and its guess → every budget-feasible strategy x and its guess; the first inequality for every guess; reason: the chain uses only feasibility of x∗ (Lemmas 3.3–3.5); specializes at x = x∗
--   - generalization: (1 − ϵ)·R(x∗) with δ = ϵ/(8ϱmax) → (1 − min(ϵ,1))·R(x) with δ = min(ϵ,1)/(8ϱmax); reason: identical for ϵ ≤ 1; for ϵ > 1 the Lean conclusion implies the printed one since R ≥ 0, and α = 2δ, β = δ stay in [0, 1] as APX(α, β) requires
--   - encoding: Dᵗᵢ(x) = Σ_{ν=1}^{Nₜ} Yᵗᵢ(x, ν), each customer making an MNL choice; Nₜ independent across periods; D̂ᵗᵢ a sum of Nₜ i.i.d. Bernoulli(q̂) variables → demandLaw: per period, Nₜ from the listed masses, then Nₜ i.i.d. categorical choices on Option (Fin n) counted per product, periods independent (Measure.pi); proxyPathLaw: per product, Nₜ then a sum of Nₜ i.i.d. Bernoulli, periods independent; reason: the paper's joint model written as PMFs; R and R̂ are the printed sums of expectations under these laws
--   - encoding: Ŷᵗᵢ(xᵢ, ν; β) ∼ Bernoulli(wᵗ_{i,xᵢ}/(1 + (1 + β)ŵₜ)) → Bernoulli with parameter clamped to [0, 1] (bern); reason: for a strategy feasible to APX(α, β) under Standing the parameter lies in [0, 1], so the clamp changes no instance the paper considers; it makes R̂ⁱ defined for every single-product strategy, which §3.6 evaluates
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §3.7, "The final revenue guarantee", p.21

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), §3.7 "The final revenue guarantee", p.21:
"R(x̂) ≥ (1 − 3δ·ϱmax)·R̂_{2δ,δ}(x̂) ≥ (1 − 3δ·ϱmax)·(1 − 2δ)·R̂_{2δ,δ}(x∗)
≥ (1 − 3δ·ϱmax)·(1 − 2δ)·(1 − 3δ)·R(x∗) ≥ (1 − 8δ·ϱmax)·R(x∗) = (1 − ϵ)·R(x∗)", with `δ = ϵ/(8ϱmax)`.

With `εh = min ε 1` and `δ = εh/(8ϱmax)`:
1. for every guess `(Γ, ŵ, ρ_single)` with `Γ ⊆ [2, T]`, `ŵ ≥ 0`, `ρ_single ≥ 0`, the strategy `x̂` the
   program derives satisfies `R(x̂) ≥ (1 − 3δϱmax)·R̂_{2δ,δ}(x̂)` (the first inequality);
2. for every budget-feasible `x`, at the guess `Γ = Γ(x)`, `ŵ` with (5) for `x` and
   `ρ_single = maxᵢ R̂ⁱ_{2δ,δ}(xᵢ)`, the program produces a candidate `x̂` with `R(x̂) ≥ (1 − εh)·R(x)`.

**Formalization Note.** `x∗` is replaced by every budget-feasible `x`. For `ε ≤ 1` the conclusion is
the printed `(1 − ϵ)·R(x∗)`; for `ε > 1` the program runs at accuracy `1` (`εh = 1`). -/
theorem revenue_guarantee {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (ε : ℝ)
    (hε : 0 < ε) :
    (∀ Γ : Finset (Fin T), (∀ t ∈ Γ, 1 ≤ t.val) → ∀ ŵ : Fin T → ℝ, (∀ t, 0 ≤ ŵ t) →
      ∀ ρs : ℝ, 0 ≤ ρs → ∀ (xh : Strategy n L T) (r : ℝ),
        I.guessCandidate (deltaOf I ε) Γ ŵ ρs = some (xh, r) →
        (1 - 3 * deltaOf I ε * I.rhoMax) * I.Rhat ŵ (deltaOf I ε) xh ≤ I.R xh) ∧
    ∀ x : Strategy n L T, I.Feasible x → ∀ ŵ : Fin T → ℝ,
      (∀ t, I.wt x t ≤ ŵ t ∧ ŵ t ≤ (1 + deltaOf I ε) * I.wt x t) → ∀ ρs : ℝ,
      (∀ i, I.Rhati ŵ (deltaOf I ε) i (col x i) ≤ ρs) →
      (∃ i, I.Rhati ŵ (deltaOf I ε) i (col x i) = ρs) →
      ∃ (xh : Strategy n L T) (r : ℝ), I.guessCandidate (deltaOf I ε) (changeSet x) ŵ ρs = some (xh, r) ∧
        (1 - min ε 1) * I.R x ≤ I.R xh := by sorry

end MenuCostPricing
