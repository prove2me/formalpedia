-- Prove2me | Theorems.Thm_LearnCollude_lemma_4
-- name    : LearnCollude.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:06.165978+00:00
-- url     : https://prove2.me/theorems/388635c5-c7fa-4d6d-b8e8-f5a6fc428f40
-- title:
--   Lemma 4 (corrected: $\delta_i/r_i(p^*)$, step-size thresholds) — relative regret of the sub-algorithms
-- statement:
--   Let both firms use the collusive sub-algorithm, with $\theta_{a,i}>1/(4K_0)$ for both $i$. Then there is a $\kappa_3>0$ such that, for both $i$ and all $T\ge1$,
--   $$
--   \Delta_i(T)\le\begin{cases}\kappa_3T^{-1/4}&\text{if }p^*=p^{col},\\ \kappa_3T^{-1/4}+\delta_i/r_i(p^*)&\text{if }p^*=p^{com}.\end{cases}
--   $$
--   Under A1.3, let both firms use the competitive sub-algorithm, with $\theta_{a,i}>1/(4K_4)$ for both $i$. Then there is a $\kappa_4>0$ such that, for both $i$ and all $T\ge1$,
--   $$
--   \Delta_i(T)\le\begin{cases}\kappa_4T^{-1/4}+\delta_i/r_i(p^*)&\text{if }p^*=p^{col},\\ \kappa_4T^{-1/4}&\text{if }p^*=p^{com}.\end{cases}
--   $$
--   The lemma translates the convergence rates of Theorems 1 and 2 into regret.
--
--   Differences from the source:
--   - correction: (16), (17) add δ_i to a relative regret → δ_i / r_i(p*); reason: a relative regret is compared with an absolute gap: for (9) with α = (3/10, 1), β₁₁ = β₂₂ = −1, β₁₂ = β₂₁ = 1/4, pmax = (3/10, 1), firm 1 has p* = pcom and δ₁ ≈ 0.0026, and its relative regret under the collusive sub-algorithm tends to δ₁/r₁(p*) ≈ 0.056 > δ₁
--   - correction: (16), (17) for every θ_a,i > 0 → (16) needs θ_a,i > 1/(4K₀), and (17) needs θ_a,i > 1/(4K₄); reason: the rates of Theorems 1 and 2 fail below the threshold (d_i(p) = 4 − p_i, θ_a,i = 1/40), and with them the T^{−1/4} rate of the regret
--   - correction: Assumption 1 → Assumption 1 plus A1.3: Σ_i (p_i − pcom_i) ∂_i r_i(p) ≤ −K₄‖p − pcom‖² on the box; reason: Assumption 1.2 allows the mean dynamics of the competitive recursion a stable periodic orbit, so the printed Theorem 2 may fail; the evidence is numerical (a grid check of Assumption 1 and an ODE integration, not a proof), and a run of the recursion itself did not settle; independently, the printed induction at (57)–(60) of the proof of Theorem 2 does not close
--   - encoding: (16), (17) under one hypothesis list → A1.3 is a hypothesis of (17) only; reason: (16) concerns the collusive recursion, and the placement of the binder changes no instance of (17)
--   - correction: E[ε_i(t) | p(t)] = 0 and E[ε_i(t)² | p(t)] ≤ σ² → the same conditional on 𝒢_t = σ(all coins, ε_j(s) for s < t); reason: noise centred given p(t) alone can be correlated with the current coin: adding B(ω_i(n) − m(p_i(t))) with m(x) = E[ω_i(n) | p_i(t) = x] at the first period of a pair biases the update by order a_n/c_n (simulated with d_i = 4 − p_i, pmax = 4: mean price 3.79 against 2.00 at n = 20000); p(t) is 𝒢_t-measurable, so the new condition implies the printed one
--   - correction: (4) compares r₂(pcol) with r₁(pcom) → r_i(pcol) > r_i(pcom) for both i, with the same index on both sides; reason: the sentence before (4) and policy (10) use the same index, and the printed (4) fails: for (9) with α = (3/2, 1), β₁₁ = β₂₂ = −1, β₁₂ = β₂₁ = 1/4, pmax = (3/2, 1), both firms gain (7/10 > 2704/3969, 11/30 > 1444/3969), so (10) selects pcol, but 11/30 ≤ 2704/3969, so the printed (4) gives pcom (checked in a verification file)
--   - generalization: a constant for the given noise process → one constant for all probability spaces and noise with the given σ²; reason: this specializes to any fixed noise; it is needed because the composite policy runs the recursions at random times
--   - reading: {ω_i^col(n)}, {ω_i^com(n)} i.i.d. sequences for each firm → the whole family, over both arms, both firms and all n, is mutually independent; reason: (5) takes a policy's random variables mutually independent, and simultaneous perturbation fails if the firms share coins
--   - generalization: (5): histories in [0, ∞) → real-valued observations; reason: Figure 2 of the paper uses Gaussian noise; nonnegative observations are a special case
--   - encoding: d_i defined on the box → d_i total and measurable, constrained on the box only; reason: p̂_i(1) ∈ (0, pmax_i) and θ_c,i < pmax_i/2 allow the first pair of prices to leave the box; the projection returns the estimates to I_i(1) after one pair, and no hypothesis is added on the box
--   - encoding: Assumption 1.2: φ₂(p₁) ∈ (0, pmax₁) → φ₂(p₁) ∈ (0, pmax₂); reason: a typo of the print, as φ₂ is a price of firm 2
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), Lemma 4, eqs. (16), (17), p. 19

import Mathlib
import Definitions.Def_LearnCollude_Policy

open Filter MeasureTheory Topology

universe u

namespace LearnCollude

/-- **Lemma 4 (corrected)** (Bounds on the relative regret of the sub-algorithms), Meylahn–den Boer,
SSRN:3741385 (PDF of 2021-12-06), eqs. (16), (17), p. 19.

If `θ_a,i > 1/(4K₀)` for both `i`, there is a `κ₃ > 0` such that, when both firms use the collusive
sub-algorithm, `Δᵢ(T) ≤ κ₃ T^{−1/4}` if `p* = pcol` and `Δᵢ(T) ≤ κ₃ T^{−1/4} + δᵢ / rᵢ(p*)` if
`p* = pcom`. If `θ_a,i > 1/(4K₄)` for both `i`, there is a `κ₄ > 0` such that, when both firms use the
competitive sub-algorithm, `Δᵢ(T) ≤ κ₄ T^{−1/4} + δᵢ / rᵢ(p*)` if `p* = pcol` and
`Δᵢ(T) ≤ κ₄ T^{−1/4}` if `p* = pcom`. Both hold for both `i` and all `T ≥ 1`.

**Formalization Note** The printed bounds add the absolute `δᵢ` to a relative regret. A1.3 is used for
the competitive part only. -/
theorem lemma_4 (M : Model) (A : Assumption1 M) (G : Gains M) (h₀ : Fin 2 → ℝ)
    (hh₀ : ∀ i, h₀ i ∈ Set.Ioo 0 (M.pmax i)) (σ2 : ℝ) (hσ2 : 0 < σ2) :
    ((∀ i, 1 / (4 * A.K₀) < G.θa i) →
      ∃ κ₃ : ℝ, 0 < κ₃ ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (ρ : Randomness μ σ2) (i : Fin 2) (T : ℕ), 1 ≤ T →
        (pStar A = A.pcol →
          relativeRegret μ A i (subPrice M G Arm.col h₀ ρ) T ≤ κ₃ * (T : ℝ) ^ (-(1 / 4) : ℝ)) ∧
        (pStar A = A.pcom →
          relativeRegret μ A i (subPrice M G Arm.col h₀ ρ) T ≤
            κ₃ * (T : ℝ) ^ (-(1 / 4) : ℝ) + revenueGap A i / M.r i (pStar A))) ∧
    (∀ B : A13 A, (∀ i, 1 / (4 * B.K₄) < G.θa i) →
      ∃ κ₄ : ℝ, 0 < κ₄ ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (ρ : Randomness μ σ2) (i : Fin 2) (T : ℕ), 1 ≤ T →
        (pStar A = A.pcol →
          relativeRegret μ A i (subPrice M G Arm.com h₀ ρ) T ≤
            κ₄ * (T : ℝ) ^ (-(1 / 4) : ℝ) + revenueGap A i / M.r i (pStar A)) ∧
        (pStar A = A.pcom →
          relativeRegret μ A i (subPrice M G Arm.com h₀ ρ) T ≤ κ₄ * (T : ℝ) ^ (-(1 / 4) : ℝ))) := by sorry

end LearnCollude
