-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_Supplement_theorem_4_13
-- name    : GreedyColoringLCA969.LowerBound.Supplement.theorem_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:36:26.931193+00:00
-- url     : https://prove2.me/theorems/fed37790-c116-492a-9187-3404bf894c84
-- title:
--   Theorem 4.13 — A single problem-independent Q(∆,k)=∆^{O(4^k)} bounds error-free per-vertex expectation and the full tail with logarithmic power 2^{k−1}.
-- statement:
--   There are a universal function $Q:\mathbb Z_+\times\mathbb Z_+\to[1,\infty)$ and an absolute integer $c\ge1$ with
--
--   $$Q(\Delta,k)\le\Delta^{c4^k}\quad(\Delta\ge2,\ k\ge1).$$
--
--   For every finite label set $L$, every extendable and radius-one locally verifiable $L$-labeling problem $P$ on all finite simple graphs, and every integer $\Delta\ge2$, there is one error-free standard-oracle LCA $A$ such that for every representation $R$ of a graph of maximum degree at most $\Delta$ and every vertex $v$,
--
--   $$\mathbb E_r[q_A(R,r,v)]\le Q(\Delta,|L|),$$
--
--   and, for every real $0<\varepsilon\le1/2$,
--
--   $$\Pr_r[q_A(R,r,v)\le Q(\Delta,|L|)(\log_2(1/\varepsilon))^{2^{|L|-1}}]\ge1-\varepsilon.$$
--
--   The same algorithm gives the expectation bound and every tail bound. The function and its exponent constant precede the problem; the algorithm can depend on the problem and degree bound, but not on the graph or $\varepsilon$. Realizability of every label is not a hypothesis. The existence of the extension rule forces $L$ nonempty, including the one-label case.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and L-valued answers in the standard adjacency-list model → Fin n identifiers and injective positive-integer return codes, with success and cost derived from the immutable shared-tape execution; reason: shifting identifiers and coding labels preserves every graph, list order, question and graph-query count
--   - encoding: Q on positive integer pairs with growth Delta^{O(4^k)} → Q on natural pairs, at least one everywhere, and an absolute c>=1 bounding Q by Delta^(c*4^k) for Delta>=2,k>=1; reason: values at zero can be set to one without changing a source instance; the absolute exponent is quantified in the proof on pp.26–27
--   - encoding: expected and high-probability query counts → nonnegative extended expectation and actual execution-cost events; reason: nontermination has infinite cost, and the same algorithm is selected before every epsilon
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), p. 23 (PDF 24), Theorem 4.13

import Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_LabelPerformance

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

theorem theorem_4_13 :
    ∃ (Q : ℕ → ℕ → ℝ) (c : ℕ), 1 ≤ c ∧
      (∀ Δ k, 1 ≤ Q Δ k) ∧
      (∀ Δ k : ℕ, 2 ≤ Δ → 1 ≤ k → Q Δ k ≤ (Δ : ℝ)^(c * 4^k)) ∧
      ∀ (L : Type) [Fintype L] (P : LabelProblem L) (F : Multiset L → L)
        (C : Set (L × Multiset L)), IsExtensionRule P F → IsLocalVerifier P C →
        ∀ Δ : ℕ, 2 ≤ Δ → ∃ A : Algorithm .standard,
          ErrorFreeOn P (finiteCode L) A Δ ∧
          ∀ (n : ℕ) (R : Representation n), MaxDegreeAtMost R.graph Δ → ∀ v,
            expectedQueries A R v ≤ ENNReal.ofReal (Q Δ (Fintype.card L)) ∧
            ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
              ENNReal.ofReal (1 - ε) ≤ tapeLaw {r | queryCost A R r v ≤
                ENNReal.ofReal (Q Δ (Fintype.card L) *
                  (log2 (1 / ε))^(2^(Fintype.card L - 1)))} := by sorry

end GreedyColoringLCA969.LowerBound.Supplement
