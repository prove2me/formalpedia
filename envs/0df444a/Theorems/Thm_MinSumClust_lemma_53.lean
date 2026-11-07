-- Prove2me | Theorems.Thm_MinSumClust_lemma_53
-- name    : MinSumClust.lemma_53
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:47:26.449041+00:00
-- url     : https://prove2.me/theorems/c981c2b2-503b-4f1c-9357-5225291fb4a4
-- title:
--   Lemma 53 — summing the bound of Lemma 52 over a partition, display (30)
-- statement:
--   Let $d$ be a pseudometric on a finite set $D$, $P_1,\dots,P_m$ disjoint clusters and $T_i\subseteq P_i$ nonempty, and let $\mathcal B$ be a partition (nonempty, pairwise disjoint parts) of a set containing every $T_i$, with $|S|\le|P_i|$ whenever $S\in\mathcal B$ and $S\cap T_i\ne\emptyset$. For each $S\in\mathcal B$ let $Z_i(S)\subseteq T_i$ be random sets satisfying the bounds of Lemma 52 with the same $a,b\ge 0$ and $p_i(S)=|S\cap T_i|/|T_i|$. Then
--
--   $$\sum_{S\in\mathcal B}\mathbb E\Bigl[2\sum_i d(S,Z_i(S))+\sum_{i,j}d(Z_i(S),Z_j(S))\Bigr]\ \le\ (2a+b)\,\mathrm{cost}(\mathcal B)+(3a+2b)\sum_i\mathrm{cost}(P_i),\qquad(30)$$
--
--   with $\mathrm{cost}(\mathcal B)=\sum_{S\in\mathcal B}\mathrm{cost}(S)$. It is applied with $\mathcal B=\mathcal S_2$ and $\mathcal B=\mathcal S_1$ in the cost bounds (33), (34).
--
--   Differences from the source:
--
--   - generalization: d is a metric → d is any pseudometric (distinct points may be at distance 0); reason: the argument uses only nonnegativity, symmetry, the zero diagonal and the triangle inequality; every metric is a pseudometric, so the paper's statement is the special case
--   - encoding: random sets Z_i(S) ⊆ T_i for each S ∈ ℬ → for each S ∈ ℬ a joint distribution μ S of (Z₁(S), …, Z_m(S)) with Z_i(S) ⊆ T_i on its support; reason: only the marginal bounds of each S enter the statement
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 53, p.52 (PDF p.54), display (30)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_pexp

namespace MinSumClust

/-- **Lemma 53**, p.52 (PDF p.54), display (30).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 53, p.52.

Let `T_i ⊆ P_i` be nonempty subsets of disjoint clusters `P₁, …, P_m`, and let `B` be a partition of
a set containing every `T_i`, with `|S| ≤ |P_i|` whenever `S ∈ B` and `S ∩ T_i ≠ ∅`. For each
`S ∈ B` let `Z_i(S) ⊆ T_i` satisfy the bounds of Lemma 52 with the same `a, b ≥ 0` and
`p_i(S) = |S ∩ T_i|/|T_i|`. Then
`∑_{S ∈ B} E[2 ∑_i d(S, Z_i(S)) + ∑_{i,j} d(Z_i(S), Z_j(S))] ≤ (2a + b) cost(B) + (3a + 2b) ∑_i cost(P_i)`,
with `cost(B) = ∑_{S ∈ B} cost(S)`.

**Formalization Note.** For each `S ∈ B` the random sets have their own joint distribution `μ S`
(only their marginal bounds matter). The parts of `B` are nonempty and pairwise disjoint. `d` is
any pseudometric. -/
theorem lemma_53 {D : Type} [Fintype D] [DecidableEq D] (d : D → D → ℝ) (hd : IsPseudometric d)
    (m : ℕ) (Pc T : Fin m → Finset D) (hP : ∀ i j, i ≠ j → Disjoint (Pc i) (Pc j))
    (hTP : ∀ i, T i ⊆ Pc i) (hT : ∀ i, (T i).Nonempty) (B : Finset (Finset D))
    (hB : (B : Set (Finset D)).PairwiseDisjoint id) (hB₀ : ∅ ∉ B)
    (hBT : ∀ i, T i ⊆ B.biUnion id)
    (hsize : ∀ S ∈ B, ∀ i, (S ∩ T i).Nonempty → S.card ≤ (Pc i).card)
    (μ : Finset D → PMF (Fin m → Finset D))
    (hsupp : ∀ S ∈ B, ∀ Z ∈ (μ S).support, ∀ i, Z i ⊆ T i) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : ∀ S ∈ B, ∀ i, ∀ u ∈ T i,
      pprob (μ S) (fun Z => u ∈ Z i) ≤ a * (((S ∩ T i).card : ℝ) / (T i).card))
    (h₂ : ∀ S ∈ B, ∀ i j, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j,
      pprob (μ S) (fun Z => u ∈ Z i ∧ v ∈ Z j) ≤
        b * (((S ∩ T i).card : ℝ) / (T i).card) * (((S ∩ T j).card : ℝ) / (T j).card)) :
    ∑ S ∈ B, pexp (μ S) (fun Z => 2 * ∑ i, distSet d S (Z i) + ∑ i, ∑ j, distSet d (Z i) (Z j)) ≤
      (2 * a + b) * ∑ S ∈ B, cost d S + (3 * a + 2 * b) * ∑ i, cost d (Pc i) := by sorry

end MinSumClust
