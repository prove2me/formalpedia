-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_Supplement_theorem_5_6
-- name    : GreedyColoringLCA969.LowerBound.Supplement.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:39:29.162704+00:00
-- url     : https://prove2.me/theorems/11208386-22f3-4421-a956-ac7c4cf403e3
-- title:
--   Theorem 5.6 — For every ∆≥3 and 0<ε<1 there is an algorithm-independent n forcing more than a 1−ε fraction of vertices to have expected query cost strictly greater than ∆/1000, for every MIS LCA gl...
-- statement:
--   For every integer $\Delta\ge3$ and real $0<\varepsilon<1$, there is a positive integer $n=n(\Delta,\varepsilon)$ such that the following holds for every randomized standard-oracle MIS LCA $A$. If its global success probability is at least $4/5$ on every $\Delta$-regular graph of every size and on every adjacency-list representation, then some represented $\Delta$-regular graph $R$ on exactly $n$ vertices satisfies both
--
--   $$A\text{ is not }(\Delta/1000,\varepsilon)\text{-efficient on }R,$$
--
--   and
--
--   $$\bigl|\{v:\mathbb E_r[q_A(R,r,v)]>\Delta/1000\}\bigr|>(1-\varepsilon)n.$$
--
--   Equivalently, strictly fewer than $\varepsilon n$ vertices have expected cost at most $\Delta/1000$. The size is fixed before the algorithm; the hard representation may depend on it. This retains constant-error algorithms, arbitrary cross-group queries, and both strict inequalities.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and L-valued answers in the standard adjacency-list model → Fin n identifiers and injective positive-integer return codes, with success and cost derived from the immutable shared-tape execution; reason: shifting identifiers and coding labels preserves every graph, list order, question and graph-query count
--   - encoding: not efficient, hence a strictly greater than 1-epsilon inefficient fraction → both negated Efficient and the strict complementary cardinality inequality, on a positive n chosen before A; reason: the finite vertex set partitions into costs at most Delta/1000 and strictly greater costs, including infinite costs
--   - generalization: LCAs return Boolean labels → arbitrary positive return codes and possible nontermination; invalid codes and nontermination fail global MIS success; reason: the published machine includes all source LCAs; for Theorem 5.6 and Lemma 5.7 invalid codes can be normalized to a Boolean label without graph queries or reducing success, while the rewiring proof of Lemma 5.4 uses only equality of returned codes; infinite executions are never light
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), p. 29 (PDF 30), Theorem 5.6

import Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_LabelPerformance

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

theorem theorem_5_6 (Δ : ℕ) (hΔ : 3 ≤ Δ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ n : ℕ, 0 < n ∧ ∀ A : Algorithm .standard,
      (∀ (m : ℕ) (R : Representation m), Regular R.graph Δ →
        ENNReal.ofReal (4 / 5 : ℝ) ≤ labelingProbability MIS boolCode A R) →
      ∃ R : Representation n, Regular R.graph Δ ∧
        ¬ Efficient A R ((Δ : ℝ) / 1000) ε ∧
        (1 - ε) * (n : ℝ) < ((Finset.univ.filter (fun v =>
          ENNReal.ofReal ((Δ : ℝ) / 1000) < expectedQueries A R v)).card : ℝ) := by sorry

end GreedyColoringLCA969.LowerBound.Supplement
