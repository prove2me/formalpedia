-- Prove2me | Theorems.Thm_MenuCostPricing_claim_B_1
-- name    : MenuCostPricing.claim_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:18.23623+00:00
-- url     : https://prove2.me/theorems/f5941aea-cc07-412f-8e40-25231c4aad22
-- title:
--   Claim B.1 — $\delta_t\le\alpha+\beta$
-- statement:
--   Let $\alpha,\beta\in[0,1]$, let $\Gamma\subseteq[2,T]$ and $\hat w$ be guesses, and let $x$ be a pricing strategy feasible to APX$(\alpha,\beta)$. Define $\delta_t$ by
--   $$
--   1-\delta_t=\frac{1+w_t(x)}{1+(1+\beta)\hat w_t}.
--   $$
--   Then $\delta_t\le\alpha+\beta$ for every period $t$.
--
--   $1-\delta_t$ is the success probability of the coupling variables $B^t_{i,\nu}$, so the claim bounds how much the proxy demand thins the true demand.
--
--   Differences from the source:
--   - generalization: the guesses Γ∗ and ŵ of §3.3 → any Γ ⊆ [2, T] and any ŵ; reason: APX(α, β) and the proof use them only as data; specializes to Γ∗ and the guessed ŵ
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Claim B.1, p.46; proof App. B.3, p.48

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Claim B.1, p.46 (proof App. B.3, p.48), with
`1 − δₜ = (1 + wₜ(x))/(1 + (1 + β)·ŵₜ)` (p.46): "δₜ ≤ α + β, for every t ∈ [T]", for a pricing
strategy `x` feasible to `APX(α, β)` with `α, β ∈ [0, 1]`.

**Formalization Note.** `Γ` is any set of periods in `[2, T]` and `ŵ` any guess vector; only
constraint (3) of APX is used by the paper's proof. -/
theorem claim_B_1 {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (Γ : Finset (Fin T))
    (hΓ : ∀ t ∈ Γ, 1 ≤ t.val) (ŵ : Fin T → ℝ) (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (x : Strategy n L T) (hx : I.APX Γ ŵ α β x) (t : Fin T) :
    1 - (1 + I.wt x t) / (1 + (1 + β) * ŵ t) ≤ α + β := by sorry

end MenuCostPricing
