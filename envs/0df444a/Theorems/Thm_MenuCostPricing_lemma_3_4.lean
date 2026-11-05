-- Prove2me | Theorems.Thm_MenuCostPricing_lemma_3_4
-- name    : MenuCostPricing.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:18.310361+00:00
-- url     : https://prove2.me/theorems/d9b59faa-5330-4187-b7f8-af54dcb4a16a
-- title:
--   Lemma 3.4 — $\hat{\mathcal R}_{2\delta,\delta}(\hat x)\ge(1-2\delta)\cdot\hat{\mathcal R}_{2\delta,\delta}(x^*)$
-- statement:
--   Fix an instance and $\delta>0$. Let $x$ be a budget-feasible strategy, let $\hat w$ satisfy $w_t(x)\le\hat w_t\le(1+\delta)w_t(x)$ for all $t$, and let $\rho_{\mathrm{single}}=\max_i\hat{\mathcal R}^i_{2\delta,\delta}(x_i)$ (8). At the guess $(\Gamma(x),\hat w,\rho_{\mathrm{single}})$:
--   1. with $\rho^*_\downarrow=\mathcal D_\rho((1-\delta)\hat{\mathcal R}_{2\delta,\delta}(x))$, $\hat{\mathcal V}(1,\vec0,\rho^*_\downarrow)\le B-|\Gamma(x)|f$ (20);
--   2. the program derives a strategy $\hat x$, and
--   $$
--   \hat{\mathcal R}_{2\delta,\delta}(\hat x)\ge(1-2\delta)\cdot\hat{\mathcal R}_{2\delta,\delta}(x).
--   $$
--
--   With $x=x^*$ this is Lemma 3.4: the rounded program loses at most a $2\delta$ fraction of the optimum's proxy reward.
--
--   Differences from the source:
--   - generalization: the optimal strategy x∗ → every budget-feasible strategy x; reason: the proof of B.7 uses only feasibility of x∗; specializes at x = x∗
--   - generalization: the conclusion R̂(x̂) ≥ (1 − 2δ)·R̂(x∗) → also (20), V̂(1, 0⃗, ρ∗↓) ≤ B − |Γ|·f, and that the program produces a candidate; reason: (20) is the first step of the paper's proof; the conjunction implies the printed conclusion
--   - encoding: ρ∗single = max_{i∈[n]} R̂ⁱ_{2δ,δ}(x∗ᵢ) (8) → ρ_single ≥ R̂ⁱ_{2δ,δ}(xᵢ) for all i, with equality for some i; reason: the same number, written without a nonemptiness proof
--   - reading: the update ρ − Dρ(R̂ⁱ_{2δ,δ}(xᵢ)) in (9), which may be negative and then is not in Dρ → the reward index is updated by truncated subtraction, i.e. clamped at 0; reason: the paper leaves the case implicit; the base case (10) only asks ρ ≤ 0, so the clamp changes no value its proofs use
--   - encoding: grid points k·δŵₜ/n ∈ Dᵗω and k·δρ∗single/n ∈ Dρ, the operators Dᵗω(·), Dρ(·) → grid states as index vectors kω (kωₜ ≤ ⌈n/δ⌉) and kρ ≤ ⌈n²/δ⌉; rounding down by roundIdx (min K ⌊a/step⌋, index 0 for a zero step); reason: the same grid points; a zero step (ŵₜ = 0 or ρ_single = 0) collapses the grid to {0}, as the paper's formula does
--   - generalization: δ = (ϵ/8)·(1/ϱmax), α = 2δ, β = δ → every δ > 0 (α = 2δ, β = δ); reason: the proofs of B.7–B.9 never bound δ from above; specializes at δ = ϵ/(8ϱmax) for every ϵ > 0
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), Lemma 3.4, p.21; proof App. B.7, pp.52–55, with (20), p.52

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), Lemma 3.4, p.21 (proof App. B.7, pp.52–55):
"R̂_{2δ,δ}(x̂) ≥ (1 − 2δ)·R̂_{2δ,δ}(x∗)", where `x̂` is the strategy the program derives for the guess
`Γ = Γ∗`, `ŵ` satisfying (5) for `x∗` and `ρ_single = ρ∗single = max_{i∈[n]} R̂ⁱ_{2δ,δ}(x∗ᵢ)` (8), p.19;
together with the bound (20), p.52, `V̂(1, 0⃗, ρ∗↓) ≤ B − |Γ∗|·f` with `ρ∗↓ = Dρ((1 − δ)·R̂_{2δ,δ}(x∗))`.

Stated for every budget-feasible `x` in place of `x∗`: with `Γ = Γ(x)`, any `ŵ` with
`wₜ(x) ≤ ŵₜ ≤ (1 + δ)·wₜ(x)` for all `t` and `ρ_single = maxᵢ R̂ⁱ_{2δ,δ}(xᵢ)`, (20) holds and the program
produces a candidate `x̂` with `R̂_{2δ,δ}(x̂) ≥ (1 − 2δ)·R̂_{2δ,δ}(x)`.

**Formalization Note.** The optimum `x∗` is one budget-feasible strategy; the paper's proof uses only
its feasibility. Stated for every `δ > 0`, which covers `δ = ϵ/(8ϱmax)` for every `ϵ > 0`. The maximum
`ρ∗single` is written as an upper bound attained by some product. -/
theorem lemma_3_4 {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (δ : ℝ) (hδ0 : 0 < δ)
    (x : Strategy n L T) (hx : I.Feasible x) (ŵ : Fin T → ℝ)
    (h5 : ∀ t, I.wt x t ≤ ŵ t ∧ ŵ t ≤ (1 + δ) * I.wt x t) (ρs : ℝ)
    (hρs_ge : ∀ i, I.Rhati ŵ δ i (col x i) ≤ ρs) (hρs_eq : ∃ i, I.Rhati ŵ δ i (col x i) = ρs) :
    I.Vhat (changeSet x) ŵ δ ρs 0 (fun _ => 0)
        (roundIdx (stepR n δ ρs) (KR n δ) ((1 - δ) * I.Rhat ŵ δ x)) ≤
      ((I.B - (changeSet x).card * I.f : ℝ) : WithTop ℝ) ∧
    ∃ (xh : Strategy n L T) (r : ℝ), I.guessCandidate δ (changeSet x) ŵ ρs = some (xh, r) ∧
      (1 - 2 * δ) * I.Rhat ŵ δ x ≤ I.Rhat ŵ δ xh := by sorry

end MenuCostPricing
