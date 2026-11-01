-- Prove2me | Theorems.Thm_LearnCollude_theorem_1
-- name    : LearnCollude.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:55.111747+00:00
-- url     : https://prove2.me/theorems/2d970415-909b-4761-b83a-a59c53f3a6f4
-- title:
--   Theorem 1 (corrected: step-size threshold for the rate, noise given the history) — convergence of the collusive sub-algorithm
-- statement:
--   Let both firms use the collusive sub-algorithm (11), under Assumption 1, with $\theta_{a,i}>0$, $\theta_{c,i}\in(0,p_i^{\max}/2)$, $\hat p_i^{col}(1)\in(0,p_i^{\max})$, and noise with $\mathbb E[\epsilon_i(t)\mid\mathcal G_t]=0$, $\mathbb E[\epsilon_i(t)^2\mid\mathcal G_t]\le\sigma^2$. Then $\hat p^{col}(n)\to p^{col}$ in probability, and $\mathbb E\|\hat p^{col}(n)-p^{col}\|^2\to0$.
--
--   If moreover $\theta_{a,i}>1/(4K_0)$ for both $i$, there is a $\kappa_1>0$, depending on the model, the tuning and $\sigma^2$ only, such that
--   $$
--   \mathbb E\|\hat p^{col}(n)-p^{col}\|^2\le\kappa_1 n^{-1/2}\qquad\text{for all }n\ge1.
--   $$
--   This is the rate that the composite policy inherits, in phases where the recursion runs at random times.
--
--   Differences from the source:
--   - correction: the rate (13) for every θ_a,i > 0 → the rate needs θ_a,i > 1/(4K₀); reason: with d_i(p) = 4 − p_i, pmax = 4, ε ≡ 0, θ_a,i = 1/40, θ_c,i = 1/2, the joint-revenue recursion started off pcol has |e_n|² ≍ n^{−1/10}; the convergence clauses keep every θ_a,i > 0
--   - correction: E[ε_i(t) | p(t)] = 0 and E[ε_i(t)² | p(t)] ≤ σ² → the same conditional on 𝒢_t = σ(all coins, ε_j(s) for s < t); reason: noise centred given p(t) alone can be correlated with the current coin: adding B(ω_i(n) − m(p_i(t))) with m(x) = E[ω_i(n) | p_i(t) = x] at the first period of a pair biases the update by order a_n/c_n (simulated with d_i = 4 − p_i, pmax = 4: mean price 3.79 against 2.00 at n = 20000); p(t) is 𝒢_t-measurable, so the new condition implies the printed one
--   - generalization: ε_i(t) drives pair n through periods 2n − 1, 2n → the same, for every Randomness structure on any probability space, which also carries the coins of the unused arm; reason: this specializes to (11), and it covers the recursion inside (10) by re-indexing the noise at random times
--   - generalization: a constant for the given noise process → one constant for all probability spaces and noise with the given σ²; reason: this specializes to any fixed noise; it is needed because the composite policy runs the recursions at random times
--   - generalization: convergence in probability → also E‖p̂col(n) − pcol‖² → 0; reason: bounded iterates: this implies convergence in probability
--   - reading: {ω_i^col(n)}, {ω_i^com(n)} i.i.d. sequences for each firm → the whole family, over both arms, both firms and all n, is mutually independent; reason: (5) takes a policy's random variables mutually independent, and simultaneous perturbation fails if the firms share coins
--   - generalization: (5): histories in [0, ∞) → real-valued observations; reason: Figure 2 of the paper uses Gaussian noise; nonnegative observations are a special case
--   - encoding: d_i defined on the box → d_i total and measurable, constrained on the box only; reason: p̂_i(1) ∈ (0, pmax_i) and θ_c,i < pmax_i/2 allow the first pair of prices to leave the box; the projection returns the estimates to I_i(1) after one pair, and no hypothesis is added on the box
--   - encoding: Assumption 1.2: φ₂(p₁) ∈ (0, pmax₁) → φ₂(p₁) ∈ (0, pmax₂); reason: a typo of the print, as φ₂ is a price of firm 2
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), Theorem 1, eq. (13), p. 16

import Mathlib
import Definitions.Def_LearnCollude_Policy

open Filter MeasureTheory Topology

universe u

namespace LearnCollude

/-- **Theorem 1 (corrected)** (Convergence of collusive sub-algorithm), Meylahn–den Boer,
SSRN:3741385 (PDF of 2021-12-06), eq. (13), p. 16.

If both firms use the collusive sub-algorithm (11), then `p̂col(n) → pcol` in probability and
`E‖p̂col(n) − pcol‖² → 0`, for all `θ_a,i > 0`. If moreover `θ_a,i > 1/(4K₀)` for both `i`, there is a
`κ₁ > 0` with `E‖p̂col(n) − pcol‖² ≤ κ₁ n^{−1/2}` for all `n ≥ 1`.

**Formalization Note** `κ₁` depends on the model, the tuning and `σ²`, not on the noise process. The
printed theorem claims the rate for every `θ_a,i > 0`, which is false. -/
theorem theorem_1 (M : Model) (A : Assumption1 M) (G : Gains M) (h₀ : Fin 2 → ℝ)
    (hh₀ : ∀ i, h₀ i ∈ Set.Ioo 0 (M.pmax i)) (σ2 : ℝ) (hσ2 : 0 < σ2) :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ρ : Randomness μ σ2),
      TendstoInMeasure μ (subEstimate M G Arm.col h₀ ρ) atTop (fun _ => A.pcol) ∧
      Tendsto (fun n : ℕ => ∫ x, ‖subEstimate M G Arm.col h₀ ρ n x - A.pcol‖ ^ 2 ∂μ) atTop (𝓝 0)) ∧
    ((∀ i, 1 / (4 * A.K₀) < G.θa i) →
      ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (ρ : Randomness μ σ2) (n : ℕ), 1 ≤ n →
        ∫ x, ‖subEstimate M G Arm.col h₀ ρ n x - A.pcol‖ ^ 2 ∂μ ≤ κ₁ * (n : ℝ) ^ (-(1 / 2) : ℝ)) := by sorry

end LearnCollude
