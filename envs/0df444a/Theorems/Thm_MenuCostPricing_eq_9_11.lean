-- Prove2me | Theorems.Thm_MenuCostPricing_eq_9_11
-- name    : MenuCostPricing.eq_9_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:18.457504+00:00
-- url     : https://prove2.me/theorems/b38314ff-6eb1-4c55-9c78-a14ae6517137
-- title:
--   (9)–(11) — the program's table is $\hat{\mathcal V}$, $\hat\rho$ is (11), and $C_{\mathrm{var}}(\hat x)=\hat{\mathcal V}(1,\vec0,\hat\rho)$
-- statement:
--   Fix an instance, $\delta>0$ and a guess $(\Gamma,\hat w,\rho_{\mathrm{single}})$ with $\Gamma\subseteq[2,T]$, $\hat w\ge0$, $\rho_{\mathrm{single}}\ge0$. For the program run on this guess:
--   1. at every grid state $(i,\omega,\rho)$, $i\in[n+1]$, $\omega\in\mathcal D_\omega$, $\rho\in\mathcal D_\rho$, the table holds $\hat{\mathcal V}(i,\omega,\rho)$ of (9)–(10);
--   2. the program reports no candidate if and only if $\{\rho\in\mathcal D_\rho:\hat{\mathcal V}(1,\vec0,\rho)\le B-|\Gamma|f\}$ is empty;
--   3. otherwise $\hat\rho$ is the maximum (11) of this set, and the strategy $\hat x$ derived by following the program from $(1,\vec0,\hat\rho)$ satisfies, along the visited states $(i,\hat\omega^{(i)},\hat\rho^{(i)})$ of (27),
--   $$
--   \hat x_i\in\mathcal F^i_0(\hat\omega^{(i)}),\qquad \hat{\mathcal V}(i,\hat\omega^{(i)},\hat\rho^{(i)})=v\,\Delta^i(\hat x_i)+\hat{\mathcal V}(i+1,\hat\omega^{(i+1)},\hat\rho^{(i+1)}),
--   $$
--   and moreover $C_{\mathrm{var}}(\hat x)=\hat{\mathcal V}(1,\vec0,\hat\rho)$ and the reward the program records is $\hat{\mathcal R}_{2\delta,\delta}(\hat x)$.
--
--   This pins down what the algorithm of Step 4 computes, which Claim B.4 and Lemmas 3.4–3.5 analyse.
--
--   Differences from the source:
--   - generalization: the guess of the optimum (Γ∗, ŵ with (5), ρ∗single) → every guess (Γ ⊆ [2, T], ŵ ≥ 0, ρ_single ≥ 0); reason: the paper's proof uses only that ρ̂ exists; specializes to the optimum's guess
--   - reading: the update ρ − Dρ(R̂ⁱ_{2δ,δ}(xᵢ)) in (9), which may be negative and then is not in Dρ → the reward index is updated by truncated subtraction, i.e. clamped at 0; reason: the paper leaves the case implicit; the base case (10) only asks ρ ≤ 0, so the clamp changes no value its proofs use
--   - reading: "the pricing strategy derived by following this program" → the strategy the program's traceback returns (first minimizer on ties); the statement holds for it; reason: the paper does not fix a tie rule; every property is stated for the returned path
--   - encoding: grid points k·δŵₜ/n ∈ Dᵗω and k·δρ∗single/n ∈ Dρ, the operators Dᵗω(·), Dρ(·) → grid states as index vectors kω (kωₜ ≤ ⌈n/δ⌉) and kρ ≤ ⌈n²/δ⌉; rounding down by roundIdx (min K ⌊a/step⌋, index 0 for a zero step); reason: the same grid points; a zero step (ŵₜ = 0 or ρ_single = 0) collapses the grid to {0}, as the paper's formula does
--   - generalization: δ = (ϵ/8)·(1/ϱmax), α = 2δ, β = δ → every δ > 0 (α = 2δ, β = δ); reason: the proofs of B.7–B.9 never bound δ from above; specializes at δ = ϵ/(8ϱmax) for every ϵ > 0
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §3.6, (9)–(10), p.20; §3.7, (11), p.21; App. B.9, (27) and "Cvar(x̂) = V̂(1, 0⃗, ρ̂)", pp.55–56

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy
import Definitions.Def_MenuCostPricing_DP
import Definitions.Def_MenuCostPricing_Algorithm

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), §3.6–§3.7, equations (9)–(11), pp.20–21, and
App. B.9, p.56 ("our recursive equations for V̂ guarantee that Cvar(x̂) = V̂(1, 0⃗, ρ̂)"): what the
program computes for one guess `(Γ, ŵ, ρ_single)` with accuracy `δ` (`α = 2δ`, `β = δ`).

1. Every cell of the program's table at a grid state `(i, ω, ρ) ∈ [n + 1] × Dω × Dρ` holds
   `V̂(i, ω, ρ)` of (9)–(10).
2. The program reports no candidate exactly when the set `{ρ ∈ Dρ : V̂(1, 0⃗, ρ) ≤ B − |Γ|·f}` of (11)
   is empty.
3. Otherwise `ρ̂` is the maximum (11) of that set, and the strategy `x̂` derived "by following this
   program, starting from the initial state (1, 0⃗, ρ̂)" (p.21) satisfies: along the visited states
   `(i, ω̂⁽ⁱ⁾, ρ̂⁽ⁱ⁾)` of (27), `x̂ᵢ ∈ Fⁱ₀(ω̂⁽ⁱ⁾)` and `x̂ᵢ` attains the minimum in (9);
   `Cvar(x̂) = V̂(1, 0⃗, ρ̂)`; and the reward the program records is `R̂_{2δ,δ}(x̂)`.

**Formalization Note.** Grid states are index vectors: `ωₜ = kωₜ·δŵₜ/n` with `kωₜ ≤ ⌈n/δ⌉` and
`ρ = kρ·δρ_single/n` with `kρ ≤ ⌈n²/δ⌉`; products are 0-based (`Vhat i` is the paper's
`V̂(i + 1, ·, ·)`). The reward update is clamped at `0` (see `Instance.Vhat`). Stated for every
`δ > 0`, which covers `δ = ϵ/(8ϱmax)` for every `ϵ > 0`. -/
theorem eq_9_11 {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (δ : ℝ) (hδ0 : 0 < δ)
    (Γ : Finset (Fin T)) (hΓ : ∀ t ∈ Γ, 1 ≤ t.val) (ŵ : Fin T → ℝ)
    (hŵ : ∀ t, 0 ≤ ŵ t) (ρs : ℝ) (hρs : 0 ≤ ρs) :
    (∀ i ≤ n, ∀ kω : Fin T → ℕ, (∀ t, kω t ≤ KW n δ) → ∀ kρ ≤ KR n δ,
      I.tableEntry δ Γ ŵ ρs i kω kρ = I.Vhat Γ ŵ δ ρs i kω kρ) ∧
    (I.guessCandidate δ Γ ŵ ρs = none ↔ I.rhoHat Γ ŵ δ ρs = ⊥) ∧
    ∀ (xh : Strategy n L T) (r : ℝ), I.guessCandidate δ Γ ŵ ρs = some (xh, r) →
      ∃ k : ℕ, I.rhoHat Γ ŵ δ ρs = (k : WithBot ℕ) ∧
        ((I.Cvar xh : ℝ) : WithTop ℝ) = I.Vhat Γ ŵ δ ρs 0 (fun _ => 0) k ∧
        r = I.Rhat ŵ δ xh ∧
        ∀ i : Fin n, I.F0 Γ ŵ δ (I.pathW ŵ δ xh i.val) i (col xh i) ∧
          I.Vhat Γ ŵ δ ρs i.val (I.pathW ŵ δ xh i.val) (I.pathR ŵ δ ρs k xh i.val) =
            ((I.v * DeltaI (col xh i) : ℝ) : WithTop ℝ) +
              I.Vhat Γ ŵ δ ρs (i.val + 1) (I.pathW ŵ δ xh (i.val + 1))
                (I.pathR ŵ δ ρs k xh (i.val + 1)) := by sorry

end MenuCostPricing
