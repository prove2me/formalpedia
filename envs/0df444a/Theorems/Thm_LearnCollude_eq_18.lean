-- Prove2me | Theorems.Thm_LearnCollude_eq_18
-- name    : LearnCollude.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:14.015673+00:00
-- url     : https://prove2.me/theorems/cdec8b98-610d-4c50-af14-c341e58903c3
-- title:
--   (18), the rate clause (b) of Theorem 3 only (corrected: step-size thresholds, A1.3, noise given the history) — $\Delta_i(T)\le\kappa_5T^{-1/5}$
-- statement:
--   Let both firms use the Composite SPSA policy with $N_c=vc+w$ and $\alpha=3/5$, under Assumption 1 and A1.3, with $\theta_{a,i}>1/(4K_0)$ and $\theta_{a,i}>1/(4K_4)$ for both $i$. Then there is a $\kappa_5>0$ such that, for both $i$ and all $T\ge1$,
--   $$
--   \Delta_i(T)\le\kappa_5T^{-1/5}.
--   $$
--   This is the rate clause of the goal theorem, stated alone. The convergence of the average prices is the other clause of the goal.
--
--   Differences from the source:
--   - correction: the rate for every θ_a,i > 0 → the rate needs θ_a,i > 1/(4K₀) and θ_a,i > 1/(4K₄); reason: with d_i(p) = 4 − p_i, pmax = 4, ε ≡ 0, θ_a,i = 1/40, θ_c,i = 1/2, p̂com(1) = (1, 2), the error obeys e_{n+1} = (1 − 1/(20n)) e_n, so |e_n|² ≍ n^{−1/10} and Δ₁(T) ≥ c T^{−1/10}; clause (a) keeps every θ_a,i > 0
--   - correction: Assumption 1 → Assumption 1 plus A1.3: Σ_i (p_i − pcom_i) ∂_i r_i(p) ≤ −K₄‖p − pcom‖² on the box; reason: Assumption 1.2 allows the mean dynamics of the competitive recursion a stable periodic orbit, so the printed Theorem 2 may fail; the evidence is numerical (a grid check of Assumption 1 and an ODE integration, not a proof), and a run of the recursion itself did not settle; independently, the printed induction at (57)–(60) of the proof of Theorem 2 does not close
--   - correction: E[ε_i(t) | p(t)] = 0 and E[ε_i(t)² | p(t)] ≤ σ² → the same conditional on 𝒢_t = σ(all coins, ε_j(s) for s < t); reason: noise centred given p(t) alone can be correlated with the current coin: adding B(ω_i(n) − m(p_i(t))) with m(x) = E[ω_i(n) | p_i(t) = x] at the first period of a pair biases the update by order a_n/c_n (simulated with d_i = 4 − p_i, pmax = 4: mean price 3.79 against 2.00 at n = 20000); p(t) is 𝒢_t-measurable, so the new condition implies the printed one
--   - correction: (4) compares r₂(pcol) with r₁(pcom) → r_i(pcol) > r_i(pcom) for both i, with the same index on both sides; reason: the sentence before (4) and policy (10) use the same index, and the printed (4) fails: for (9) with α = (3/2, 1), β₁₁ = β₂₂ = −1, β₁₂ = β₂₁ = 1/4, pmax = (3/2, 1), both firms gain (7/10 > 2704/3969, 11/30 > 1444/3969), so (10) selects pcol, but 11/30 ≤ 2704/3969, so the printed (4) gives pcom (checked in a verification file)
--   - reading: t_c = Σ_{i ≤ c} N_i with five phases → cycle c has length L_c = max(N_c, 8⌊N_c^α⌋); reason: the printed t_c overlaps when 8⌊N_c^α⌋ > N_c, e.g. v = 1, w = 0, c = 1; p. 43 says the fifth phase then has length zero; this changes finitely many cycles
--   - reading: phase 5 of unspecified parity → an odd phase 5 ends with the first period of a pair and no update, and the next pair of that arm uses the same counter; reason: (10) makes the update in the even periods only
--   - generalization: a constant for the given noise process → one constant for all probability spaces and noise with the given σ²; reason: this specializes to any fixed noise; it is needed because the composite policy runs the recursions at random times
--   - reading: {ω_i^col(n)}, {ω_i^com(n)} i.i.d. sequences for each firm → the whole family, over both arms, both firms and all n, is mutually independent; reason: (5) takes a policy's random variables mutually independent, and simultaneous perturbation fails if the firms share coins
--   - generalization: (5): histories in [0, ∞) → real-valued observations; reason: Figure 2 of the paper uses Gaussian noise; nonnegative observations are a special case
--   - encoding: d_i defined on the box → d_i total and measurable, constrained on the box only; reason: p̂_i(1) ∈ (0, pmax_i) and θ_c,i < pmax_i/2 allow the first pair of prices to leave the box; the projection returns the estimates to I_i(1) after one pair, and no hypothesis is added on the box
--   - encoding: (10): p̂_k^col, ω_k in the exploitation update and n^com = n^col + 1; Assumption 1.2: φ₂(p₁) ∈ (0, pmax₁) → p̂_i^col, ω_i, n^com = n^com + 1, and φ₂(p₁) ∈ (0, pmax₂); reason: typos of the print
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), eq. (18), p. 20

import Mathlib
import Definitions.Def_LearnCollude_Policy

open Filter MeasureTheory Topology

universe u

namespace LearnCollude

/-- **The rate clause of Theorem 3**, Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06), eq. (18),
p. 20. This is clause (b) of `theorem_3` alone.

If both firms use the Composite SPSA policy with `θ_a,i > 1/(4K₀)` and `θ_a,i > 1/(4K₄)`, there is a
`κ₅ > 0` with `Δᵢ(T) ≤ κ₅ T^{−1/5}` for both `i` and all `T ≥ 1`. -/
theorem eq_18 (M : Model) (A : Assumption1 M) (B : A13 A) (G : Gains M) (S : Schedule)
    (h₀ : Arm → Fin 2 → ℝ) (hh₀ : IsInitial M h₀) (σ2 : ℝ) (hσ2 : 0 < σ2)
    (hθ : ∀ i, 1 / (4 * A.K₀) < G.θa i ∧ 1 / (4 * B.K₄) < G.θa i) :
    ∃ κ₅ : ℝ, 0 < κ₅ ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ρ : Randomness μ σ2) (i : Fin 2) (T : ℕ), 1 ≤ T →
      relativeRegret μ A i (compositePrice M G S h₀ ρ) T ≤ κ₅ * (T : ℝ) ^ (-(1 / 5) : ℝ) := by sorry

end LearnCollude
