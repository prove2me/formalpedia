-- Prove2me | Theorems.Thm_MenuCostPricing_lemma_3_5
-- name    : MenuCostPricing.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:03.609631+00:00
-- url     : https://prove2.me/theorems/2bd8bf2a-8008-4a72-ae3b-31cd66a6a569
-- title:
--   Lemma 3.5 — $\hat x$ is feasible to APX$(2\delta,\delta)$
-- statement:
--   Fix an instance, $\delta>0$ and a guess $(\Gamma,\hat w,\rho_{\mathrm{single}})$ with $\Gamma\subseteq[2,T]$, $\hat w\ge0$ and $\rho_{\mathrm{single}}\ge0$. If $\hat\rho$ of (11) exists, the strategy $\hat x$ the program derives for this guess is feasible to APX$(2\delta,\delta)$ for $(\Gamma,\hat w)$:
--   $$
--   C_{\mathrm{var}}(\hat x)\le B-|\Gamma|f,\qquad \Delta_{t-1,t}(\hat x)=0\ \ (t\notin\Gamma),\qquad (1-2\delta)\hat w_t\le w_t(\hat x)\le(1+\delta)\hat w_t\ \ \forall t.
--   $$
--
--   Combined with constraints (3)–(4), every candidate of the algorithm is budget-feasible.
--
--   Differences from the source:
--   - generalization: the guess of the optimum (Γ∗, ŵ with (5), ρ∗single) → every guess (Γ ⊆ [2, T], ŵ ≥ 0, ρ_single ≥ 0); reason: the paper's proof uses only that ρ̂ exists; specializes to the optimum's guess
--   - reading: the update ρ − Dρ(R̂ⁱ_{2δ,δ}(xᵢ)) in (9), which may be negative and then is not in Dρ → the reward index is updated by truncated subtraction, i.e. clamped at 0; reason: the paper leaves the case implicit; the base case (10) only asks ρ ≤ 0, so the clamp changes no value its proofs use
--   - encoding: grid points k·δŵₜ/n ∈ Dᵗω and k·δρ∗single/n ∈ Dρ, the operators Dᵗω(·), Dρ(·) → grid states as index vectors kω (kωₜ ≤ ⌈n/δ⌉) and kρ ≤ ⌈n²/δ⌉; rounding down by roundIdx (min K ⌊a/step⌋, index 0 for a zero step); reason: the same grid points; a zero step (ŵₜ = 0 or ρ_single = 0) collapses the grid to {0}, as the paper's formula does
--   - generalization: δ = (ϵ/8)·(1/ϱmax), α = 2δ, β = δ → every δ > 0 (α = 2δ, β = δ); reason: the proofs of B.7–B.9 never bound δ from above; specializes at δ = ϵ/(8ϱmax) for every ϵ > 0
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Lemma 3.5, p.21; proof App. B.9, pp.55–56

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Lemma 3.5, p.21 (proof App. B.9, pp.55–56): "The
pricing strategy x̂ is feasible to APX(2δ, δ)."

Stated for the strategy `x̂` the program derives for **every** guess `(Γ, ŵ, ρ_single)` with
`Γ ⊆ [2, T]`, `ŵ ≥ 0` and `ρ_single ≥ 0` at which `ρ̂` exists: `x̂` is feasible to `APX(2δ, δ)` for that
`Γ` and `ŵ`.

**Formalization Note.** The paper states it at the guess of the optimum; its proof uses only that
`ρ̂` exists (the nonemptiness remark of B.9 is where it uses the optimum). Stated for every `δ > 0`,
which covers `δ = ϵ/(8ϱmax)` for every `ϵ > 0`. -/
theorem lemma_3_5 {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (δ : ℝ) (hδ0 : 0 < δ)
    (Γ : Finset (Fin T)) (hΓ : ∀ t ∈ Γ, 1 ≤ t.val) (ŵ : Fin T → ℝ)
    (hŵ : ∀ t, 0 ≤ ŵ t) (ρs : ℝ) (hρs : 0 ≤ ρs) (xh : Strategy n L T) (r : ℝ)
    (hxh : I.guessCandidate δ Γ ŵ ρs = some (xh, r)) :
    I.APX Γ ŵ (2 * δ) δ xh := by sorry

end MenuCostPricing
