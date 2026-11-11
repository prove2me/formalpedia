-- Prove2me | Theorems.Thm_KMedianPP_Tight_lemma_4_1
-- name    : KMedianPP.Tight.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:03:24.380225+00:00
-- url     : https://prove2.me/theorems/fc974393-7dd8-4619-920c-b5c6e9d76c51
-- title:
--   Lemma 4.1 — $U_{\mathrm{new}}\le U$ on a miss, $\le U-u_i$ on a hit of $P_i$, and $\mathbb E[U_{\mathrm{new}}\mid S,\text{hit}]\le\frac{r-1}{r}U$
-- statement:
--   Fix a state with $r$ unsettled clusters and total balanced mass $U$ (a balancing construction with (P1)–(P3) is fixed). Then
--   1. on a miss (any sampled point with positive miss probability), $U_{\mathrm{new}}\le U$;
--   2. on a hit of $P_i$ (any sampled point of $P_i$ with positive hit probability), $U_{\mathrm{new}}\le U-u_i$;
--   3. if a hit has positive probability, $\mathbb E[U_{\mathrm{new}}\mid S,\text{hit}]\le\frac{r-1}{r}\,U$.
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
--   - encoding: r = number of unsettled clusters → `unsettledCount H = |univ \ H|`; reason: same number
--   - encoding: "On a miss", "On a hit of P_i" → for every input index i with `missProb … i > 0` (resp. `hitProb … i > 0`, cluster σ i); reason: these are exactly the outcomes of a miss (resp. a hit of P_{σ i})
--   - encoding: E[U_new | S, hit] → `hitExp … (balTotal σ b) S H`, under 0 < Σ_i hitProb i; reason: conditional expectation given an event of positive probability
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), p. 14 (PDF 16), Lemma 4.1

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling
import Definitions.Def_KMedianPP_Tight_Balancing

set_option autoImplicit false

namespace KMedianPP.Tight

/-- Lemma 4.1 (p. 14): fix a state with `r` unsettled clusters and total balanced mass `U`. On a
miss, `U_new ≤ U`. On a hit of `P_i`, `U_new ≤ U - u_i`. Conditioned on a hit,
`E[U_new | S, hit] ≤ (r - 1)/r · U`.
A state `(S, H)` has the cluster of some current center (the first center) settled, `σ i ∈ H`
for some `i ∈ S` (§3, p. 9). -/
theorem lemma_4_1 {M : Type*} [MetricSpace M] {n k : ℕ} (X : Fin n → M) (σ : Fin n → Fin k)
    (c : Fin k → M) (ℓ α : ℝ) (hℓ : 0 < ℓ) (b : Finset (Fin n) → Fin n → ℝ)
    (hb : IsBalancingConstruction X σ c ℓ α b)
    (S : Finset (Fin n)) (H : Finset (Fin k)) (hSH : ∃ i ∈ S, σ i ∈ H) :
    (∀ i : Fin n, 0 < missProb X σ ℓ b S H i →
      balTotal σ b (insert i S) H ≤ balTotal σ b S H) ∧
    (∀ i : Fin n, 0 < hitProb X σ ℓ b S H i →
      balTotal σ b (insert i S) (insert (σ i) H) ≤ balTotal σ b S H - balMass σ b S (σ i)) ∧
    (0 < ∑ i, hitProb X σ ℓ b S H i →
      hitExp X σ ℓ b (balTotal σ b) S H ≤
        ((unsettledCount H : ℝ) - 1) / (unsettledCount H : ℝ) * balTotal σ b S H) := by sorry

end KMedianPP.Tight
