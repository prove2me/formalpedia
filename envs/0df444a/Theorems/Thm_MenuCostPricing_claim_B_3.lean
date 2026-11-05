-- Prove2me | Theorems.Thm_MenuCostPricing_claim_B_3
-- name    : MenuCostPricing.claim_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:14.116333+00:00
-- url     : https://prove2.me/theorems/600cbee9-1b6d-4211-8f3b-38fe31a12974
-- title:
--   Claim B.3 — $\hat{\mathcal R}^i_{\alpha,\beta}(x_i)\le(1+(\alpha+\beta)\,p^i_{\max}/p^i_{\min})\cdot R_i(x)$
-- statement:
--   Let $\alpha,\beta\in[0,1]$, let $\Gamma\subseteq[2,T]$ and $\hat w$ be guesses, and let $x$ be feasible to APX$(\alpha,\beta)$. For every product $i$,
--   $$
--   \hat{\mathcal R}^i_{\alpha,\beta}(x_i)\le\Big(1+(\alpha+\beta)\cdot\frac{p^i_{\max}}{p^i_{\min}}\Big)\cdot R_i(x),
--   $$
--   where $R_i(x)=\sum_t\mathbb E[\min\{U^t_i(x),D^t_i(x)\}]\,p_{i,x^t_i}$ is the expected revenue from product $i$.
--
--   This product-by-product bound gives the upper half of Lemma 3.3.
--
--   Differences from the source:
--   - generalization: the guesses Γ∗ and ŵ of §3.3 → any Γ ⊆ [2, T] and any ŵ; reason: APX(α, β) and the proof use them only as data; specializes to Γ∗ and the guessed ŵ
--   - encoding: Dᵗᵢ(x) = Σ_{ν=1}^{Nₜ} Yᵗᵢ(x, ν), each customer making an MNL choice; Nₜ independent across periods; D̂ᵗᵢ a sum of Nₜ i.i.d. Bernoulli(q̂) variables → demandLaw: per period, Nₜ from the listed masses, then Nₜ i.i.d. categorical choices on Option (Fin n) counted per product, periods independent (Measure.pi); proxyPathLaw: per product, Nₜ then a sum of Nₜ i.i.d. Bernoulli, periods independent; reason: the paper's joint model written as PMFs; R and R̂ are the printed sums of expectations under these laws
--   - encoding: Ŷᵗᵢ(xᵢ, ν; β) ∼ Bernoulli(wᵗ_{i,xᵢ}/(1 + (1 + β)ŵₜ)) → Bernoulli with parameter clamped to [0, 1] (bern); reason: for a strategy feasible to APX(α, β) under Standing the parameter lies in [0, 1], so the clamp changes no instance the paper considers; it makes R̂ⁱ defined for every single-product strategy, which §3.6 evaluates
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Claim B.3, p.48; proof App. B.5, pp.49–51

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Claim B.3, p.48 (proof App. B.5, pp.49–51): for a
pricing strategy `x` feasible to `APX(α, β)` with `α, β ∈ [0, 1]`, "For every product i ∈ [n], we have
R̂ⁱ_{α,β}(xᵢ) ≤ (1 + (α + β)·pⁱmax/pⁱmin)·Rᵢ(x)", where `Rᵢ(x)` is the expected revenue from product `i`.

**Formalization Note.** `Γ` is any set of periods in `[2, T]` and `ŵ` any guess vector. -/
theorem claim_B_3 {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (Γ : Finset (Fin T))
    (hΓ : ∀ t ∈ Γ, 1 ≤ t.val) (ŵ : Fin T → ℝ) (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (x : Strategy n L T) (hx : I.APX Γ ŵ α β x) (i : Fin n) :
    I.Rhati ŵ β i (col x i) ≤ (1 + (α + β) * (I.pmax i / I.pmin i)) * I.Ri x i := by sorry

end MenuCostPricing
