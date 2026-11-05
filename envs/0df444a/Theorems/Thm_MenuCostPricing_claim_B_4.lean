-- Prove2me | Theorems.Thm_MenuCostPricing_claim_B_4
-- name    : MenuCostPricing.claim_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:00.541073+00:00
-- url     : https://prove2.me/theorems/8b23a145-ce0d-4a99-8da3-97ad606cd413
-- title:
--   Claim B.4 — $\hat{\mathcal R}_{2\delta,\delta}(\hat x)\ge\hat\rho$
-- statement:
--   Fix an instance, $\delta>0$ and a guess $(\Gamma,\hat w,\rho_{\mathrm{single}})$ with $\Gamma\subseteq[2,T]$, $\hat w\ge0$, $\rho_{\mathrm{single}}\ge0$ at which $\hat\rho$ of (11) exists. The strategy $\hat x$ the program derives for this guess satisfies
--   $$
--   \hat{\mathcal R}_{2\delta,\delta}(\hat x)\ge\hat\rho .
--   $$
--
--   Together with $\hat\rho\ge(1-2\delta)\hat{\mathcal R}_{2\delta,\delta}(x^*)$ this gives Lemma 3.4.
--
--   Differences from the source:
--   - generalization: the guess of the optimum (Γ∗, ŵ with (5), ρ∗single) → every guess (Γ ⊆ [2, T], ŵ ≥ 0, ρ_single ≥ 0); reason: the paper's proof uses only that ρ̂ exists; specializes to the optimum's guess
--   - reading: the update ρ − Dρ(R̂ⁱ_{2δ,δ}(xᵢ)) in (9), which may be negative and then is not in Dρ → the reward index is updated by truncated subtraction, i.e. clamped at 0; reason: the paper leaves the case implicit; the base case (10) only asks ρ ≤ 0, so the clamp changes no value its proofs use
--   - encoding: grid points k·δŵₜ/n ∈ Dᵗω and k·δρ∗single/n ∈ Dρ, the operators Dᵗω(·), Dρ(·) → grid states as index vectors kω (kωₜ ≤ ⌈n/δ⌉) and kρ ≤ ⌈n²/δ⌉; rounding down by roundIdx (min K ⌊a/step⌋, index 0 for a zero step); reason: the same grid points; a zero step (ŵₜ = 0 or ρ_single = 0) collapses the grid to {0}, as the paper's formula does
--   - generalization: δ = (ϵ/8)·(1/ϱmax), α = 2δ, β = δ → every δ > 0 (α = 2δ, β = δ); reason: the proofs of B.7–B.9 never bound δ from above; specializes at δ = ϵ/(8ϱmax) for every ϵ > 0
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Claim B.4, p.53; proof App. B.8, p.55

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Claim B.4, p.53 (proof App. B.8, p.55):
"R̂_{2δ,δ}(x̂) ≥ ρ̂", for the strategy `x̂` the program derives for a guess `(Γ, ŵ, ρ_single)` at which `ρ̂`
of (11) exists.

**Formalization Note.** Stated for every guess with `ŵ ≥ 0`, `ρ_single ≥ 0`, `Γ ⊆ [2, T]` (the paper
states it at the guess of the optimum; its proof uses only the existence of `ρ̂`). `ρ̂` is the grid
point `k·δρ_single/n` of index `k`. Stated for every `δ > 0`. -/
theorem claim_B_4 {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (δ : ℝ) (hδ0 : 0 < δ)
    (Γ : Finset (Fin T)) (hΓ : ∀ t ∈ Γ, 1 ≤ t.val) (ŵ : Fin T → ℝ)
    (hŵ : ∀ t, 0 ≤ ŵ t) (ρs : ℝ) (hρs : 0 ≤ ρs) (xh : Strategy n L T) (r : ℝ)
    (hxh : I.guessCandidate δ Γ ŵ ρs = some (xh, r)) (k : ℕ)
    (hk : I.rhoHat Γ ŵ δ ρs = (k : WithBot ℕ)) :
    (k : ℝ) * stepR n δ ρs ≤ I.Rhat ŵ δ xh := by sorry

end MenuCostPricing
