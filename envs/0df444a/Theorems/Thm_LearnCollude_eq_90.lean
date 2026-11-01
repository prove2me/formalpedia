-- Prove2me | Theorems.Thm_LearnCollude_eq_90
-- name    : LearnCollude.eq_90
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:03.034109+00:00
-- url     : https://prove2.me/theorems/53538793-095d-4689-9279-dfc5ed87aa76
-- title:
--   (90), (93) (corrected: exponent, ties) — the regret per cycle
-- statement:
--   Let both firms use the Composite SPSA policy under Assumption 1 and A1.3, with $\theta_{a,i}>1/(4K_0)$ and $\theta_{a,i}>1/(4K_4)$. There is a $C>0$ such that, for both firms and every cycle $c\ge1$,
--   $$
--   \sum_{t\in\text{cycle }c}\mathbb E[r_i(p^*)-r_i(p(t))]\le C\,c^{3/5}.
--   $$
--   If there is no one-sided tie, also $\sum_{t\in\text{cycle }c}\mathbb E|r_i(p^*)-r_i(p(t))|\le C\,c^{3/5}$. Summing over the $O(\sqrt T)$ cycles gives the rate of Theorem 3.
--
--   Differences from the source:
--   - correction: (89): the bracket κ^var (Σ⌊N_l^α⌋)^{−1/2} + (pmax)²σ²/(2⌊N_c^α⌋²), squared → the first power, with ⌊N_c^α⌋^{−1} in place of ⌊N_c^α⌋^{−2}; reason: the average of 2⌊N_c^α⌋ terms of variance at most (pmax σ)² has variance of order 1/⌊N_c^α⌋, attained by noise with a value of size ⌊N_c^α⌋ with probability of order ⌊N_c^α⌋^{−2} per period, and Chebyshev's inequality gives the first power of the variance
--   - encoding: (90) as an explicit sum of three terms, for c > c_{T_c} → the bound C c^{3/5}, for all c ≥ 1; reason: with α = 3/5 the corrected right side of (90) is of exact order c^{3/5}, its first term being r_max N_c^α
--   - generalization: (90) with division by δ = min{δ₁, δ₂}, so without ties → the signed bound also at ties; reason: this contains the case without ties
--   - correction: (93) bounds E|r_i(p*) − r_i(p(t))| in every case → the absolute form excludes one-sided ties; the signed form of (8) holds always; reason: at a one-sided tie the favoured firm has |r_i(p*) − r_i(pcol)| = δ_i > 0 on an arm chosen with non-vanishing probability
--   - correction: no condition on θ_a,i → θ_a,i > 1/(4K₀) and θ_a,i > 1/(4K₄); reason: the bound rests on the rates (13), (14), which fail below these thresholds (d_i(p) = 4 − p_i, θ_a,i = 1/40)
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
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), eqs. (90), (93), p. 46

import Mathlib
import Definitions.Def_LearnCollude_Policy

open Filter MeasureTheory Topology

universe u

namespace LearnCollude

/-- **The regret per cycle (corrected)**, Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06),
eqs. (90), (93), p. 46.

Under the step-size thresholds, there is a `C > 0` such that, for both firms and every cycle `c`,
`Σ_{t in cycle c} E[rᵢ(p*) − rᵢ(p(t))] ≤ C c^{3/5}`, and, if there is no one-sided tie, also
`Σ_{t in cycle c} E|rᵢ(p*) − rᵢ(p(t))| ≤ C c^{3/5}`.

**Formalization Note** The bound is the order of (90) after the correction of (89), with `α = 3/5`. It
is stated without excluding ties `rᵢ(pcol) = rᵢ(pcom)`, which the printed proof, dividing by
`δ = min{δ₁, δ₂}`, does not treat. The absolute values of the printed (93) need the exclusion of
one-sided ties: at such a tie the favoured firm's revenue differs from `rᵢ(p*)` by a constant, on the
arm chosen with non-vanishing probability. -/
theorem eq_90 (M : Model) (A : Assumption1 M) (B : A13 A) (G : Gains M) (S : Schedule)
    (h₀ : Arm → Fin 2 → ℝ) (hh₀ : IsInitial M h₀) (σ2 : ℝ) (hσ2 : 0 < σ2)
    (hθ : ∀ i, 1 / (4 * A.K₀) < G.θa i ∧ 1 / (4 * B.K₄) < G.θa i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ρ : Randomness μ σ2) (i : Fin 2) (c : ℕ), 1 ≤ c →
      (∑ t ∈ Finset.Ioc (S.s c) (S.s (c + 1)),
        ∫ x, (M.r i (pStar A) - M.r i (compositePrice M G S h₀ ρ t x)) ∂μ ≤
          C * (c : ℝ) ^ (3 / 5 : ℝ)) ∧
      (NoOneSidedTie A → ∑ t ∈ Finset.Ioc (S.s c) (S.s (c + 1)),
        ∫ x, |M.r i (pStar A) - M.r i (compositePrice M G S h₀ ρ t x)| ∂μ ≤
          C * (c : ℝ) ^ (3 / 5 : ℝ)) := by sorry

end LearnCollude
