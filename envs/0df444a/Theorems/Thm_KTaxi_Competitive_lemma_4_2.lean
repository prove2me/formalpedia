-- Prove2me | Theorems.Thm_KTaxi_Competitive_lemma_4_2
-- name    : KTaxi.Competitive.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:57.167402+00:00
-- url     : https://prove2.me/theorems/1d855bc6-6c01-483a-8b94-5cec0ff7222c
-- title:
--   Lemma 4.2 — Property 4.1 implies Algorithm 1 is $(\sum_m\alpha_m)$-competitive
-- statement:
--   Let $\alpha_1,\dots,\alpha_k\ge0$ be coefficients for which Property 4.1 holds on the metric space $V$. Then Algorithm 1 is $\bigl(\sum_{m=1}^k\alpha_m\bigr)$-competitive against adaptive online adversaries, with the initial potential as additive constant: for all initial configurations $x_0$ (algorithm; its ordered list is $x_0$ in label order) and $y_0$ (adversary), every adaptive online adversary and every horizon $T$,
--   $$
--   \mathbb E[\mathrm{ALG}]\le\Bigl(\sum_{m=1}^k\alpha_m\Bigr)\mathbb E[\mathrm{ADV}]+\Phi(x_0,y_0).
--   $$
--   When both players start in the same configuration, $\Phi(x_0,x_0)=0$ and this is the paper's bound $\mathbb E[\mathrm{ALG}]\le(\sum_m\alpha_m)\mathbb E[\mathrm{ADV}]$. Lemma 4.2 reduces competitiveness to the one-round inequality of Property 4.1.
--
--   **Formalization Note** Costs are `algCost`/`advCost` of `algorithm1` in `ℝ≥0∞`; the real constants enter through `ENNReal.ofReal`.
--
--   Differences from the source:
--   - generalization: α_1 > ⋯ > α_k > 0 → α_m ≥ 0 for 1 ≤ m ≤ k; reason: the proof uses only nonnegativity of the coefficients
--   - generalization: E[ALG] ≤ (∑_m α_m)E[ADV] from a common start (initial potential 0) → E[ALG] ≤ (∑_m α_m)E[ADV] + Φ(x₀, y₀) for arbitrary starts x₀, y₀; reason: Φ(x₀, x₀) = 0, so the common-start case is the paper's bound; the explicit constant gives (∑α)-competitiveness
--   - generalization: the adaptive online adversary chooses each request from the algorithm's past actions → the adversary's move is any function of the full history of the algorithm's outcomes, including its internal states; reason: an action-only adversary is the special case that ignores the states, so the bound for all adversaries specializes to the paper's class
--   - generalization: the adversary moves one taxi to r to serve each request → before serving, the adversary may also move any of its taxis to a new configuration z, paying the distances travelled; reason: choosing z equal to the current configuration recovers the source; the 1-Lipschitz matching-cost bound also charges repositioning to the adversary movement cost
--   - encoding: adaptive online adversary (possibly randomized) → deterministic adversaries: a function of the history; reason: a randomized adversary is a mixture of deterministic ones and E[ALG] ≤ ρE[ADV] + β is preserved by averaging
--   - encoding: E[ALG], E[ADV] over the adversary's (finite) request sequence → expected costs in ℝ≥0∞ computed on the game tree with at most T rounds (the adversary may stop earlier), for every T; reason: every finite request sequence has some length T; ℝ≥0∞ avoids undefined expectations
--   - encoding: Algorithm 1 starts from an arbitrary ordered list → it starts with the list ordered by label (state = identity permutation); reason: the labelled start x₀ is arbitrary, so every initial ordered list is realised by relabelling
--   - generalization: k ≥ 2 (standing assumption, PDF p. 4) → k ≥ 1, including the one-taxi case; reason: the statement also holds for one taxi and specializes to every k ≥ 2; at k = 1 the scan is the identity, the matching has one edge, and any lower-level sum is empty
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Lemma 4.2 and its proof, PDF p. 7 (printed p. 6)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Potential

namespace KTaxi.Competitive

/-- **Lemma 4.2** (PDF p. 7). If Property 4.1 holds for nonnegative coefficients
`α_1, …, α_k`, then Algorithm 1 is `(∑_m α_m)`-competitive against adaptive online
adversaries, with additive constant the initial potential: for all initial configurations
`x₀` (algorithm, ordered by label) and `y₀` (adversary), every adaptive online adversary and
every horizon `T`,
`E[ALG] ≤ (∑_{m=1}^k α_m) · E[ADV] + Φ(x₀, y₀)`. -/
theorem lemma_4_2 {V : Type*} [MetricSpace V] {k : ℕ} [NeZero k] (α : ℕ → ℝ)
    (hα : ∀ m ∈ Finset.Icc 1 k, 0 ≤ α m) (hP : Property41 V k α)
    (x₀ y₀ : Fin k → V) (adv : Adversary V k (algorithm1 V k).State) (T : ℕ) :
    algCost (algorithm1 V k) adv T x₀ y₀ ≤
      ENNReal.ofReal (∑ m ∈ Finset.Icc 1 k, α m) * advCost (algorithm1 V k) adv T x₀ y₀ +
        ENNReal.ofReal (potential α x₀ y₀) := by sorry

end KTaxi.Competitive
