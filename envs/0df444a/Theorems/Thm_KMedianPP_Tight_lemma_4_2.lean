-- Prove2me | Theorems.Thm_KMedianPP_Tight_lemma_4_2
-- name    : KMedianPP.Tight.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:03:25.132964+00:00
-- url     : https://prove2.me/theorems/6fff63d2-0d20-4a27-8330-adfeeaf3926b
-- title:
--   Lemma 4.2 — $A_{\mathrm{new}}\le A$ on a miss and $\mathbb E[A_{\mathrm{new}}\mid S,\text{hit of }P_i]\le A$
-- statement:
--   Fix a state (a balancing construction with constant $\alpha$ and (P1)–(P3) is fixed) and let $A=\sum_{P_j\text{ settled}}\mathrm{cost}(P_j,C)+\alpha\sum_{P_j\text{ unsettled}}\varphi(P_j)$ be the miss proxy. Then
--   1. on a miss, $A_{\mathrm{new}}\le A$;
--   2. for every unsettled $P_i$ whose hit has positive probability, $\mathbb E[A_{\mathrm{new}}\mid S,\text{hit of }P_i]\le A$.
--
--   Differences from the source:
--   - encoding: a finite (multi)set X ⊆ M of input points → `X : Fin n → M` (input point i is `X i`; repeated points allowed); reason: a finite multiset is an indexed family; same instances
--   - encoding: current center set C ⊆ M, D(x) = d(x, C) → the indices `S : Finset (Fin n)` of the sampled input points, `D(x) = distTo X S x` (minimum over S); reason: D^ℓ-sampling only ever samples input points; same distances
--   - generalization: a fixed optimal solution with clusters P_1, …, P_k and optimal centers c*_1, …, c*_k (§2, p. 9) → any reference clustering: `σ : Fin n → Fin k` (P_j = {i : σ i = j}) and centers `c : Fin k → M`, with ϕ(P_j) = `phi X σ c ℓ j`; reason: the analysis never uses optimality or nearest-center assignment (only d*_x = d(x, c*_j) and the triangle inequality); an optimal solution is one such clustering, so the statement specializes to the source's
--   - encoding: §2 standing assumption: a fixed distance exponent ℓ > 0 → hypothesis `0 < ℓ`; reason: the section's standing assumption made explicit
--   - encoding: D(x)^ℓ, (d*_x)^ℓ for real ℓ > 0 → `Real.rpow` (`^` with a real exponent) of nonnegative reals; reason: same values
--   - encoding: §4 standing assumption: a balancing construction with constant α_ℓ satisfying (P1)–(P3) (pp. 10, 14) → balanced masses `b : Finset (Fin n) → Fin n → ℝ` with `IsBalancingConstruction X σ c ℓ α b`: 0 ≤ b(x) ≤ D(x)^ℓ, (P1), (P2), (P3) for every cluster P_j that can be unsettled at the center set S (`CanBeUnsettled σ S j`: some current center outside P_j); reason: the properties as stated on p. 10, for unsettled clusters; the first center settles its own cluster, so P_j can be unsettled at S exactly when some center of S lies outside P_j; a construction is given by its balanced masses
--   - generalization: a state S of the process (centers, settled/unsettled clusters and masses, reached by the process) → any pair (S, H) of a set S of center indices and a set H : Finset (Fin k) of settled clusters (the others unsettled) in which the cluster of some current center is settled (`∃ i ∈ S, σ i ∈ H`: the first center settles its cluster, §3 p. 9); reason: every reachable state is such a pair; the statement also covers unreachable pairs
--   - encoding: a sample x ∈ P of an unsettled cluster is a hit with probability b(x)/D(x)^ℓ, otherwise a miss; samples from settled clusters are misses → `hitProb`/`missProb` S H i = (hit / miss mass at x_i) / cost(C); a hit of P_{σ i} moves to (S ∪ {i}, H ∪ {σ i}), a miss to (S ∪ {i}, H); reason: the joint law of (sampled point, hit/miss) of p. 11 and p. 14
--   - encoding: "On a miss" → for every input index i with `missProb … i > 0`; reason: exactly the outcomes of a miss
--   - encoding: E[A_new | S, hit of P_i], P_i ∈ U → `hitExpAt … (missProxy …) j S H` for j ∉ H, under 0 < Σ_{x∈P_j} hitProb; reason: conditional expectation given an event of positive probability
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 15 (PDF 17), Lemma 4.2

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling
import Definitions.Def_KMedianPP_Tight_Balancing

set_option autoImplicit false

namespace KMedianPP.Tight

/-- Lemma 4.2 (p. 15): fix a state. On a miss, `A_new ≤ A`. On a hit of an unsettled cluster
`P_j`, `E[A_new | S, hit of P_j] ≤ A`.
A state `(S, H)` has the cluster of some current center (the first center) settled, `σ i ∈ H`
for some `i ∈ S` (§3, p. 9). -/
theorem lemma_4_2 {M : Type*} [MetricSpace M] {n k : ℕ} (X : Fin n → M) (σ : Fin n → Fin k)
    (c : Fin k → M) (ℓ α : ℝ) (hℓ : 0 < ℓ) (b : Finset (Fin n) → Fin n → ℝ)
    (hb : IsBalancingConstruction X σ c ℓ α b)
    (S : Finset (Fin n)) (H : Finset (Fin k)) (hSH : ∃ i ∈ S, σ i ∈ H) :
    (∀ i : Fin n, 0 < missProb X σ ℓ b S H i →
      missProxy X σ c ℓ α (insert i S) H ≤ missProxy X σ c ℓ α S H) ∧
    (∀ j : Fin k, j ∉ H → 0 < ∑ i ∈ cluster σ j, hitProb X σ ℓ b S H i →
      hitExpAt X σ ℓ b (missProxy X σ c ℓ α) j S H ≤ missProxy X σ c ℓ α S H) := by sorry

end KMedianPP.Tight
