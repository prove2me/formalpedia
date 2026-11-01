-- Prove2me | Theorems.Thm_OnlineWass_one_step_dual
-- name    : OnlineWass.one_step_dual
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:14.4907+00:00
-- url     : https://prove2.me/theorems/7b180a9e-c76c-44d5-8a04-bf57d5d443b9
-- title:
--   One-step dual inequalities
-- statement:
--   Under the model's hypotheses, let $\gamma_t\in[0,1]^m$, let $\mathrm{sel}$ be a tie-break rule and $\theta_t\sim\mathcal P_t$ independent. For each $t$ and every profile,
--
--   $$
--   \|p_{t+1}\|_2^2\le\|p_t\|_2^2+\frac1T\|g(\tilde x_t;\theta_t)-\gamma_t\|_2^2-\frac2{\sqrt T}\,p_t^\top(\gamma_t-g(\tilde x_t;\theta_t)),
--   $$
--
--   and, in expectation,
--
--   $$
--   \mathbb E_{p_t}\bigl[p_t^\top(\gamma_t-\mathcal P_t g(\tilde x_t;\theta_t))\bigr]\le\frac{\sqrt T}2\bigl(\mathbb E[\|p_t\|_2^2]-\mathbb E[\|p_{t+1}\|_2^2]\bigr)+\frac m{2\sqrt T}.
--   $$
--
--   Here $\mathcal P_t g(\tilde x_t;\theta_t)$ is the expectation over a fresh $\theta\sim\mathcal P_t$ with the price held fixed. Summed over $t$ this telescopes to the $\sqrt T$ term of (32).
--
--   Differences from the source:
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: x̃ₜ = argmax with no rule for ties → any jointly measurable tie-break rule sel; reason: every solver of line 4 that reads (pₜ, θₜ) is such a rule, and the bound holds for each
--   - generalization: γ̂ₜ → any input γₜ ∈ [0,1]ᵐ; reason: γ̂ₜ is an average of values of g, so it is such an input
--   - encoding: periods t = 1, …, T, p₁, p_{T+1} → t : Fin T is period t + 1; p₁ is index 0, p_{T+1} is index T; reason: Lean indices; same instances
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Proof of Theorem 3, p.56

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_igd

open MeasureTheory

namespace OnlineWass

/-- **The one-step dual inequalities, Jiang, Li & Zhang, arXiv:2012.06961v3, p.56.** Pathwise,
`‖pₜ₊₁‖₂² ≤ ‖pₜ‖₂² + (1/T)‖g(x̃ₜ; θₜ) − γₜ‖₂² − (2/√T) pₜᵀ(γₜ − g(x̃ₜ; θₜ))`, and, in expectation,
`𝔼_{pₜ}[pₜᵀ(γₜ − 𝒫ₜ g(x̃ₜ; θₜ))] ≤ (√T/2)(𝔼[‖pₜ‖₂²] − 𝔼[‖pₜ₊₁‖₂²]) + m/(2√T)`.

**Formalization Note.** In the second display `𝒫ₜ g(x̃ₜ; θₜ)` is the integral over a fresh `θ ∼ 𝒫ₜ` with the
price held fixed, and the outer integral averages over the price, as printed: that the price at period
`t` is a function of `θ₁, …, θₜ₋₁` is what makes this follow from the first display. `γₜ ∈ [0, 1]ᵐ` holds
for `γ̂ₜ`. `t : Fin T` is period `t + 1`. -/
theorem one_step_dual {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (hA : Assumption1ab M) (hρ : DistEqRho M) (hT : 0 < T)
    (γ : Fin T → Fin m → ℝ) (hγ0 : ∀ t i, 0 ≤ γ t i) (hγ1 : ∀ t i, γ t i ≤ 1)
    (sel : (Fin m → ℝ) → Θ → Fin k → ℝ) (hsel : IsTieBreak M sel)
    (P : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (P t)] (t : Fin T) :
    (∀ H : Fin T → Θ,
      ∑ i, price M sel γ H (t + 1) i ^ 2 ≤
        ∑ i, price M sel γ H t i ^ 2 +
          (1 / (T : ℝ)) * ∑ i, (M.g (virtualAction M sel γ H t) (H t) i - γ t i) ^ 2 -
          (2 / √(T : ℝ)) * ∑ i, price M sel γ H t i *
            (γ t i - M.g (virtualAction M sel γ H t) (H t) i)) ∧
    ∫ H, ∑ i, price M sel γ H t i *
          (γ t i - ∫ θ, M.g (sel (price M sel γ H t) θ) θ i ∂P t) ∂Measure.pi P ≤
      (√(T : ℝ) / 2) *
          (∫ H, ∑ i, price M sel γ H t i ^ 2 ∂Measure.pi P -
            ∫ H, ∑ i, price M sel γ H (t + 1) i ^ 2 ∂Measure.pi P) +
        (m : ℝ) / (2 * √(T : ℝ)) := by sorry

end OnlineWass
