-- Prove2me | Theorems.Thm_KnownFidelity_Rank_lemma_5_10
-- name    : KnownFidelity.Rank.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:49.952571+00:00
-- url     : https://prove2.me/theorems/33e89710-6d41-4606-8628-7445fea87e8a
-- title:
--   Lemma 5.10 — long-cycle estimate $\mathbb E_bN_k\le (m^k/k)(B/r)^{2k-2}$ and $\delta_b\le m\theta^K/((K+1)(1-\theta))$
-- statement:
--   Let $a\in\mathbb R^r_{\ge0}$ with $u_1=\sum_ia_i=1$ and $\max_ia_i\le B/r$, let $m\in\mathbb N$, and let $\mathbb P$ be the law on $S_m$ with $\mathbb P(\pi)\propto\prod_{d\in\mathrm{Cycles}(\pi)}u_{|d|}^2$, $u_k=\sum_i a_i^k$ (Eq. (59)). Write $N_k(\pi)$ for the number of $k$-cycles of $\pi$. Then for every $k\ge1$
--
--   $$\mathbb E\,N_k\ \le\ \frac{m^k}{k}\Big(\frac Br\Big)^{2k-2},$$
--
--   and consequently, if $\theta=mB^2/r^2<1$, then for every $K$
--
--   $$\delta:=\mathbb P\big[\text{some cycle of }\pi\text{ has length}>K\big]\ \le\ \frac{m\theta^K}{(K+1)(1-\theta)} .$$
--
--   In the proof of Proposition 5.11 the mass $\delta_b$ is the only place where the two laws $\mathbb P_0,\mathbb P_1$ can differ.
--
--   **Formalization Note** Cycles include fixed points (1-cycles).
--
--   Differences from the source:
--   - generalization: the vectors a^{(b)} fixed in §5.4 (from Proposition 5.2) and an integer m ≥ 1 → any nonnegative a ∈ ℝ^r with u_1 = 1 and entries ≤ B/r, and any m : ℕ; reason: the lemma's proof uses only these properties; the paper's vectors satisfy them, so the Lean statement specializes to the source
--   - encoding: E_b N_k and P_b[some cycle has length greater than K] → finite sums over Equiv.Perm (Fin m) weighted by cycleProb, cycles = π.partition.parts (fixed points included); reason: S_m is finite; the partition of a permutation is its multiset of all cycle lengths
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Lemma 5.10, p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_cycleProb

namespace KnownFidelity.Rank

open Classical in
/-- **Lemma 5.10 (long-cycle estimate).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Lemma 5.10, printed p. 20 (PDF p. 22): "Suppose u_{b,1} = 1 and max_i a^{(b)}_i ≤ B/r.
Then E_b N_k ≤ (m^k/k)(B/r)^{2k−2}. (60) Consequently, if θ = mB²/r² < 1, then
δ_b := P_b[some cycle has length greater than K] ≤ mθ^K/((K + 1)(1 − θ)). (61)" Here P_b is the
law (59) on S_m and N_k(π) is the number of k-cycles of π.

For a nonnegative vector `a ∈ ℝ^r` with `Σ_i a_i = 1` and entries at most `B/r`, under the law
`P(π) = cycleProb a π` on `S_m`: (60) for every `k ≥ 1`, `E N_k ≤ (m^k/k)(B/r)^{2k−2}`; and (61)
for every `K`, if `θ = mB²/r² < 1`, the probability that some cycle of `π` has length `> K` is at
most `mθ^K/((K+1)(1−θ))`.

**Formalization Note.** The cycles of `π` include its fixed points: `π.partition.parts` is the
multiset of all cycle lengths, so `N_k(π)` is the multiplicity of `k` in it. The vector is any
vector with the hypotheses of the lemma and the standing nonnegativity of §5.4 (the paper applies
it to the vectors of Proposition 5.2). -/
theorem lemma_5_10 {r m : ℕ} (a : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hu : powerSum a 1 = 1)
    (B : ℝ) (hB : ∀ i, a i ≤ B / r) :
    (∀ k : ℕ, 1 ≤ k →
      ∑ π : Equiv.Perm (Fin m), cycleProb a π * (π.partition.parts.count k : ℝ) ≤
        (m : ℝ) ^ k / k * (B / r) ^ (2 * k - 2)) ∧
    (m * B ^ 2 / r ^ 2 < 1 → ∀ K : ℕ,
      ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∃ l ∈ π.partition.parts, K < l),
          cycleProb a π ≤
        m * (m * B ^ 2 / r ^ 2) ^ K / ((K + 1) * (1 - m * B ^ 2 / r ^ 2))) := by sorry

end KnownFidelity.Rank
