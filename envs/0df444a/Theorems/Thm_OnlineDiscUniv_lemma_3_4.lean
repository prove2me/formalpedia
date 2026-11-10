-- Prove2me | Theorems.Thm_OnlineDiscUniv_lemma_3_4
-- name    : OnlineDiscUniv.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:01.200073+00:00
-- url     : https://prove2.me/theorems/279e74d3-e692-415c-9db9-c3e0f3ef1dcc
-- title:
--   Lemma 3.4 — delocalizing the drift by a Rademacher perturbation
-- statement:
--   Fix $s>2$ and $\Lambda>0$. Let $b_k$ be determined before the fresh Rademacher vector $\eta_k\in\{\pm1\}^M$ is drawn, and $\tilde r_k=b_k+\gamma\eta_k$, $\gamma>0$ (3.29). Conditional on the information available at that time,
--   $$
--   \mathbb P\Big(\|\tilde r_k\|_2^2<\tfrac12\big(\|b_k\|_2^2+\gamma^2M\big)\Big)\le2e^{-cM}.\qquad(3.30)
--   $$
--   If in addition $M^{-1}\sum_i|b_{k,i}|^s\le\Lambda^s$, then on the complement of this event
--   $$
--   \frac{\|\tilde r_k\|_\infty}{\|\tilde r_k\|_2}\le C_{\Lambda,\gamma}M^{1/s-1/2}.\qquad(3.31)
--   $$
--   Along $M/N\to\alpha$, if the empirical moment bound holds at every step, a union bound gives (3.31) simultaneously over $O(N)$ steps with probability $1-e^{-\Omega(N)}$. Moreover,
--   $$
--   \max_{i\le M,\ \ell\le N}\Big|\frac\gamma N\sum_{k=1}^\ell\eta_{k,i}\Big|=O_{\mathbb P}\Big(\gamma\sqrt{\frac{\log M}{N}}\Big)=o_{\mathbb P}(1),\qquad(3.32)
--   $$
--   and
--   $$
--   \frac{\|b_k+\gamma\eta_k\|_2}{\sqrt M}\le\frac{\|b_k\|_2}{\sqrt M}+\gamma.\qquad(3.33)
--   $$
--
--   The perturbation spreads the drift over all coordinates, which the coupling error bounds (3.17) need, at the cost of a vanishing terminal drift.
--
--   Differences from the source:
--   - encoding: conditional on the information available at that time (3.30), b_k determined before η_k → (3.30) for a fixed b ∈ ℝ^M and η with law radVec M; reason: η_k is independent of the past, so the conditional probability is this probability evaluated at b = b_k (Fubini)
--   - reading: the constant c in 2e^{−cM} → one absolute c > 0, chosen before γ, M and b; reason: the paper does not say what c depends on; the absolute constant is the stronger reading (the proof gives c = 1/8)
--   - encoding: (3.31) on the complement of this event → (3.31) for every η ∈ {±1}^M outside the event of (3.30); C chosen after (s, Λ, γ), before M; reason: the event is a set of values of η; same statement
--   - reading: union bound: (3.31) simultaneously over O(N) steps with probability 1 − e^{−Ω(N)}, if the empirical moment bound holds at every step → for every C₀ there are c' > 0 and N₀ such that for N ≥ N₀ and J ≤ C₀N steps, with b_k a measurable function of independent extra randomness and of η_j, j < k, and the moment bound a.s. at every step, P(∃k: ratio > C M^{1/s−1/2}) ≤ e^{−c'N}, with the C of (3.31); reason: spells out O(N), Ω(N) and "determined before η_k"
--   - encoding: O_P(γ√(log M/N)) = o_P(1) → ∀ε ∃C ∃N₀ ∀N ≥ N₀: P(max > Cγ√(log M_N/N)) ≤ ε; and ∀ε > 0, P(max > ε) → 0; reason: the definitions of O_P and o_P; the max over i, ℓ is written as an existential event
--   - encoding: ‖·‖_∞, ‖·‖₂ → Mathlib's sup norm on Fin M → ℝ; √(∑ x_i²); reason: same norms
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Lemma 3.4, (3.29)–(3.33), pp.9–10 (PDF pp.10–11)

import Mathlib
import Definitions.Def_OnlineDiscUniv_radVec

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Lemma 3.4** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.10, PDF p.11).
Fix `s > 2`, `Λ > 0`; let `b_k` be determined before the fresh Rademacher vector `η_k` is drawn and
`r̃_k = b_k + γη_k` (3.29). Conditional on the information available,
`P(‖r̃_k‖_2² < ½(‖b_k‖_2² + γ²M)) ≤ 2e^{−cM}` (3.30). If `M^{−1}∑_i |b_{k,i}|^s ≤ Λ^s`, then on the
complement `‖r̃_k‖_∞/‖r̃_k‖_2 ≤ C_{Λ,γ} M^{1/s−1/2}` (3.31). Along `M/N → α`, if the empirical moment
bound holds at every step, (3.31) holds simultaneously over the `N` steps with probability
`1 − e^{−Ω(N)}`. Moreover `max_{i≤M, ℓ≤N} |(γ/N)∑_{k=1}^{ℓ} η_{k,i}| = O_P(γ√(log M/N)) = o_P(1)`
(3.32), and `‖b_k + γη_k‖_2/√M ≤ ‖b_k‖_2/√M + γ` (3.33).

**Formalization Note** (3.30) is stated for a fixed `b` and `η` with the law `radVec M` (the
conditional statement follows by independence); `c > 0` is absolute (chosen before `γ, M, b`).
(3.31) is stated for every `η ∈ {±1}^M` outside the event of (3.30). In the union-bound clause the
drifts `b_k` are measurable functions of an independent extra randomness `w` and of
`η_1, …, η_{k−1}` only (0-based: of the `η_j`, `j < k`), the moment bound holds almost surely at
every step, and the constant is the same `C_{Λ,γ}` as in (3.31). `O_P` and `o_P` are spelled out
as tightness and convergence in probability. `‖·‖_∞` is the sup norm, `‖x‖_2 = √(∑_i x_i²)`. -/
theorem lemma_3_4 :
    (∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) (b : Fin M → ℝ) (γ : ℝ), 0 < γ →
      radVec M {η | ∑ i, (b i + γ * η i) ^ 2 < (1 / 2) * (∑ i, b i ^ 2 + γ ^ 2 * M)} ≤
        ENNReal.ofReal (2 * Real.exp (-c * M))) ∧
    (∀ s Λ γ : ℝ, 2 < s → 0 < Λ → 0 < γ → ∃ C : ℝ,
      (∀ (M : ℕ) (b η : Fin M → ℝ), (1 / (M : ℝ)) * ∑ i, |b i| ^ s ≤ Λ ^ s →
        (∀ i, η i = 1 ∨ η i = -1) →
        ¬ (∑ i, (b i + γ * η i) ^ 2 < (1 / 2) * (∑ i, b i ^ 2 + γ ^ 2 * M)) →
        ‖b + γ • η‖ / Real.sqrt (∑ i, (b i + γ * η i) ^ 2) ≤
          C * (M : ℝ) ^ (1 / s - 1 / 2)) ∧
      ∀ α : ℝ, 0 < α → ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
        ∀ C₀ : ℝ, ∃ c' : ℝ, 0 < c' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ J : ℕ, (J : ℝ) ≤ C₀ * N →
          ∀ (W : Type) [MeasurableSpace W] (PW : Measure W) [IsProbabilityMeasure PW]
            (b : Fin J → W × (Fin J → Fin (Mseq N) → ℝ) → (Fin (Mseq N) → ℝ)),
            (∀ k, Measurable (b k)) →
            (∀ k w η η', (∀ j : Fin J, j < k → η j = η' j) → b k (w, η) = b k (w, η')) →
            (∀ᵐ q ∂(PW.prod (Measure.pi fun _ : Fin J => radVec (Mseq N))), ∀ k,
              (1 / (Mseq N : ℝ)) * ∑ i, |b k q i| ^ s ≤ Λ ^ s) →
            (PW.prod (Measure.pi fun _ : Fin J => radVec (Mseq N)))
              {q | ∃ k, C * (Mseq N : ℝ) ^ (1 / s - 1 / 2) <
                ‖b k q + γ • q.2 k‖ / Real.sqrt (∑ i, (b k q i + γ * q.2 k i) ^ 2)} ≤
              ENNReal.ofReal (Real.exp (-c' * N))) ∧
    (∀ γ α : ℝ, 0 < γ → 0 < α → ∀ Mseq : ℕ → ℕ,
      Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Measure.pi fun _ : Fin N => radVec (Mseq N))
          {η | ∃ (i : Fin (Mseq N)) (ℓ : ℕ), ℓ ≤ N ∧
            C * γ * Real.sqrt (Real.log (Mseq N) / N) <
              |(γ / N) * ∑ k : Fin N, if (k : ℕ) < ℓ then η k i else 0|} ≤
          ENNReal.ofReal ε) ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N : ℕ => (Measure.pi fun _ : Fin N => radVec (Mseq N))
          {η | ∃ (i : Fin (Mseq N)) (ℓ : ℕ), ℓ ≤ N ∧
            ε < |(γ / N) * ∑ k : Fin N, if (k : ℕ) < ℓ then η k i else 0|}) atTop (𝓝 0)) ∧
    (∀ (M : ℕ) (b η : Fin M → ℝ) (γ : ℝ), 0 < γ → (∀ i, η i = 1 ∨ η i = -1) →
      Real.sqrt (∑ i, (b i + γ * η i) ^ 2) / Real.sqrt M ≤
        Real.sqrt (∑ i, b i ^ 2) / Real.sqrt M + γ) := by sorry

end OnlineDiscUniv
