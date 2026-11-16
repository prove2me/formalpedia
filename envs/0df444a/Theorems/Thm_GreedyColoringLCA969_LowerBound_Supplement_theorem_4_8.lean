-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_Supplement_theorem_4_8
-- name    : GreedyColoringLCA969.LowerBound.Supplement.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:34:34.865164+00:00
-- url     : https://prove2.me/theorems/d2887a41-d9c6-4fe0-9b2e-83b34fa6f9fd
-- title:
--   Theorem 4.8 — Both error-free upper bounds for every extendable radius-one locally verifiable Boolean labeling problem on all graphs: average O(∆²), and polynomial expected cost at every vertex.
-- statement:
--   Let $P$ be an extendable and radius-one locally verifiable Boolean-labeling problem on all finite simple graphs. Both following guarantees hold.
--
--   1. There are one error-free standard-oracle LCA $A$ and a constant $K>0$ such that, for every integer $\Delta\ge0$ and every represented graph $R$ of maximum degree at most $\Delta$,
--
--   $$\frac1{|V|}\sum_{v\in V}\mathbb E_r[q_A(R,r,v)]\le K(\Delta+1)^2.$$
--
--   The empty-graph average is zero.
--
--   2. There are $Q:\mathbb Z_+\to\mathbb Z_+$, $K>0$ and an integer $d\ge0$, with $Q(\Delta)\le K\Delta^d$ for all positive $\Delta$, such that for each positive $\Delta$ there is an error-free LCA $A_\Delta$ satisfying
--
--   $$\mathbb E_r[q_{A_\Delta}(R,r,v)]\le Q(\Delta)$$
--
--   for every size, representation and vertex of a graph of maximum degree at most $\Delta$. The algorithms in the two clauses may differ. These are respectively an average quadratic guarantee and a polynomial guarantee at every vertex.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and L-valued answers in the standard adjacency-list model → Fin n identifiers and injective positive-integer return codes, with success and cost derived from the immutable shared-tape execution; reason: shifting identifiers and coding labels preserves every graph, list order, question and graph-query count
--   - encoding: O(Delta^2) average complexity and O(poly(Delta)) per-vertex complexity → a uniform K(Delta+1)^2 bound for one average-cost LCA and a positive-integer Q bounded by K Delta^d for the per-degree LCA family; reason: Corollary 4.4 on p.15 supplies (Delta+1)^2 and a polynomial function; quantified constants are outside all inputs and no numerical polynomial degree is invented
--   - encoding: expected query counts → nonnegative extended expectations and an empty-graph average of zero; reason: infinite costs stay infinite; the empty graph has no questions
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), p. 18 (PDF 19), Theorem 4.8

import Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_LabelPerformance

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

theorem theorem_4_8 (P : LabelProblem Bool) (F : Multiset Bool → Bool)
    (C : Set (Bool × Multiset Bool)) (hext : IsExtensionRule P F)
    (hloc : IsLocalVerifier P C) :
    (∃ (A : Algorithm .standard) (K : ℝ), 0 < K ∧
      ∀ (Δ n : ℕ) (R : Representation n), MaxDegreeAtMost R.graph Δ →
        labelingProbability P boolCode A R = 1 ∧
        averageQueries A R ≤ ENNReal.ofReal (K * ((Δ : ℝ) + 1)^2)) ∧
    (∃ (Q : ℕ+ → ℕ+) (K : ℝ) (d : ℕ), 0 < K ∧
      (∀ Δ : ℕ+, (Q Δ : ℝ) ≤ K * (Δ : ℝ)^d) ∧
      ∀ Δ : ℕ+, ∃ A : Algorithm .standard, ErrorFreeOn P boolCode A Δ ∧
        ∀ (n : ℕ) (R : Representation n), MaxDegreeAtMost R.graph (Δ : ℝ) →
          ∀ v, expectedQueries A R v ≤ (Q Δ : ℝ≥0∞)) := by sorry

end GreedyColoringLCA969.LowerBound.Supplement
