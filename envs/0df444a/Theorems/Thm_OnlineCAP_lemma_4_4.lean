-- Prove2me | Theorems.Thm_OnlineCAP_lemma_4_4
-- name    : OnlineCAP.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:53.011233+00:00
-- url     : https://prove2.me/theorems/23cfc655-78f6-41c8-a367-4b13346c5c13
-- title:
--   Lemma 4.4 — low-SCC online sampler: Pr[e ∈ J_t] ≤ O(log(A log N)/B)
-- statement:
--   For every constant $C_A$ there are constants $K$ and $N_0$ with the following property. Let $V$ be a finite universe of size $N\ge N_0$, and let $B,A$ be reals with
--   $$N^{1/3}\le B\le N,\qquad 1\le A\le C_A\log N .$$
--   Then there is a randomized online algorithm maintaining an increasing set $J_t\subseteq V$ such that for every online request sequence $Q_1,\dots,Q_t$ (chosen obliviously) with $|Q_i|\ge B$ for all $i$, whose set system $(V,\{Q_1,\dots,Q_t\})$ has shallow cell complexity $\varphi(m,\kappa)\le A\kappa^2$:
--
--   1. $J_t$ hits every $Q_i$, $i\le t$, for every outcome of the coins;
--   2. for every element $e\in V$,
--   $$\Pr[e\in J_t]\le K\cdot\frac{\log(A\log N)}{B}.$$
--
--   The paper obtains this as a specialization of [BGK26, Theorem 5.5]; it is the sampler that Algorithm 2 feeds with heavy virtual queries.
--
--   Differences from the source:
--   - generalization: a universal constant C_A, to be determined later → every constant C_A, with K and N₀ depending on C_A; reason: the source fixes C_A = 2C_dom/ln 2 (p.20), a special case
--   - encoding: Pr[e ∈ J_t] ≤ O(log(A log N)/B) → ≤ K · log(A log N)/B for N ≥ N₀; reason: the O-constant and the threshold "for sufficiently large N" (proof, p.16); natural logarithms
--   - encoding: an infinite request sequence Q₁, Q₂, … with G = {Q₁, Q₂, …} → every finite request list whose own set system satisfies the hypotheses; reason: the guarantee at time t concerns the prefix, and every prefix of a sequence satisfying the hypotheses satisfies them (shallow cell complexity passes to subfamilies); conversely a list extends to a sequence by repeating its last request
--   - reading: there exists a randomized online algorithm (for an oblivious request sequence) → one algorithm, depending only on V, B, A, chosen before the request sequence, feasible for every outcome of the coins; reason: "oblivious online hitting set request sequence" and "maintaining an increasing hitting set"; choosing the algorithm after the sequence would make the lemma trivial
--   - encoding: the set system (V, G) with φ(m, κ) ≤ Aκ² for all m, κ ≥ 1 → HasSCC with φ(m, κ) = Aκ²; reason: shallow cell complexity bounded by φ is monotone in φ, so the two are equivalent
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Lemma 4.4, p.15 (from [BGK26, Theorem 5.5])

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_HasSCC

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Lemma 4.4 (Low SCC Online Sampler).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Lemma 4.4, p.15 (PDF p.15): "Let V be a universe
of size N, and let N^{1/3} ≤ B ≤ N and 1 ≤ A ≤ C_A log N be parameters (for a universal constant
C_A, to be determined later). Let Q1, Q2, . . . be an oblivious online hitting set request sequence
satisfying |Qt| ≥ B for every t. Let G = {Q1, Q2, . . .}, and assume that the set system (V, G)
has shallow cell complexity bounded by φ(m, κ) ≤ Aκ² for all m, κ ≥ 1. Then there exists a
randomized online algorithm maintaining an increasing hitting set Jt ⊆ V such that
Pr[e ∈ Jt] ≤ O(log(A log N)/B) for every element e ∈ V and every finite horizon t." The paper
proves it as a special case of [BGK26, Theorem 5.5] (arXiv:2603.14293v1).

For every constant `C_A` there are `K` and `N₀` such that: for every finite universe `V` with
`N = |V| ≥ N₀` and all reals `B, A` with `N^{1/3} ≤ B ≤ N` and `1 ≤ A ≤ C_A log N`, there is one
randomized online algorithm such that for every request list `Q₁, …, Q_t` of sets of size at least
`B` whose set system has shallow cell complexity at most `Aκ²`, the purchased set `J_t` hits every
`Q_i` for every outcome of the coins and `Pr[e ∈ J_t] ≤ K · log(A log N) / B` for every `e ∈ V`.

**Formalization Note.** The algorithm is chosen before the requests (oblivious adversary), and
the request list is finite: a request sequence's prefixes are such lists, with the same or a
smaller set system (shallow cell complexity is inherited by subfamilies). The `O(·)` is a
constant `K` and a threshold `N₀` depending only on `C_A`; logarithms are natural. -/
theorem lemma_4_4 (C_A : ℝ) :
    ∃ (K : ℝ) (N₀ : ℕ), ∀ (V : Type) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ B A : ℝ, (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3) ≤ B → B ≤ Fintype.card V → 1 ≤ A →
        A ≤ C_A * Real.log (Fintype.card V) →
        ∃ J : RandOnlineAlg V (Finset V), ∀ s : List (Finset V), (∀ Q ∈ s, B ≤ Q.card) →
          HasSCC {Q | Q ∈ s} (fun _ κ => A * (κ : ℝ) ^ 2) →
          (∀ ω, ∀ Q ∈ s, ∃ e ∈ J.buy ω s, e ∈ Q) ∧
          ∀ e : V, J.μ.real {ω | e ∈ J.buy ω s} ≤
            K * (Real.log (A * Real.log (Fintype.card V)) / B) := by sorry

end OnlineCAP
