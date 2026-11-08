-- Prove2me | Theorems.Thm_MenuCostPricing_claim_B_2
-- name    : MenuCostPricing.claim_B_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:36:10.518052+00:00
-- url     : https://prove2.me/theorems/c9b9edb4-c95e-47a5-9a82-5f030bb4d407
-- title:
--   Claim B.2 — under the coupling $\hat Y=B\cdot Y$: $\hat D^t_i\le D^t_i$ and $U^t_i\le\hat U^t_i$
-- statement:
--   Fix a realization of the arrivals $N_t$, of the indicators $Y^t_i(x,\nu)$ that customer $\nu$ of period $t$ is interested in product $i$, and of the coupling variables $B^t_{i,\nu}\in\{0,1\}$. Let
--   $$
--   D^t_i=\sum_{\nu=1}^{N_t}Y^t_i(x,\nu),\qquad \hat D^t_i=\sum_{\nu=1}^{N_t}B^t_{i,\nu}\,Y^t_i(x,\nu),
--   $$
--   and let $U^t_i=[u^1_i-\sum_{\tau<t}D^\tau_i]^+$ and $\hat U^t_i=[u^1_i-\sum_{\tau<t}\hat D^\tau_i]^+$. Then for every period $t$ and product $i$:
--   1. $D^t_i\ge\hat D^t_i$;
--   2. $U^t_i\le\hat U^t_i$.
--
--   In particular both hold with probability one under the coupling of Appendix B.2.
--
--   Differences from the source:
--   - generalization: with probability 1, for x feasible to APX(α, β) and β ≥ 0 → for every realization of (Nₜ, Yᵗᵢ, Bᵗᵢ,ν), with no hypothesis on x, α, β; reason: the proof of B.4 is pathwise; the almost-sure statement follows for every law of the coupled variables
--   - encoding: customers ν = 1, …, Nₜ; Ŷ = B·Y with 0/1 variables → customers ν = 0, …, Nₜ − 1; Boolean indicators, Ŷ = B && Y; reason: Lean convention; the same sums
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Claim B.2, p.46; coupling App. B.2, p.46; proof App. B.4, p.49

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Claim B.2, p.46 (proof App. B.4, p.49), for the
coupling `Ŷᵗᵢ(xᵢ, ν; β) = Bᵗ_{i,ν}·Yᵗᵢ(x, ν)` of App. B.2: "1. Dᵗᵢ(x) ≥ D̂ᵗᵢ(xᵢ; β) with probability 1.
2. Uᵗᵢ(x) ≤ Ûᵗᵢ(xᵢ; β) with probability 1."

Stated pathwise: for every realization of the arrivals `Nₜ`, the interest indicators `Yᵗᵢ(x, ν)` and
the coupling variables `Bᵗ_{i,ν}`, with `Dᵗᵢ = Σ_{ν=1}^{Nₜ} Yᵗᵢ(x, ν)`, `D̂ᵗᵢ = Σ_{ν=1}^{Nₜ} Bᵗ_{i,ν}Yᵗᵢ(x, ν)`
and the inventories `Uᵗᵢ`, `Ûᵗᵢ` of (1) (starting from `u¹ᵢ`), `D̂ᵗᵢ ≤ Dᵗᵢ` and `Uᵗᵢ ≤ Ûᵗᵢ`.

**Formalization Note.** A pathwise inequality holds with probability `1` under every law of the
coupled variables. The pathwise statement uses neither APX feasibility nor `β ≥ 0`. -/
theorem claim_B_2 {n T : ℕ} (u : Fin n → ℕ) (N : Fin T → ℕ) (Y Bc : Fin T → Fin n → ℕ → Bool) :
    (∀ t i, coupledProxyDemand N Y Bc t i ≤ coupledDemand N Y t i) ∧
    (∀ t i, invLevel (u i) (fun τ => coupledDemand N Y τ i) t ≤
      invLevel (u i) (fun τ => coupledProxyDemand N Y Bc τ i) t) := by sorry

end MenuCostPricing
